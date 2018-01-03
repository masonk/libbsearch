#![feature(range_contains)]
use std::cmp::Ordering;
use std::cmp::Ordering::{Less, Greater, Equal};

// The least idx of a slice for which ordering(array[idx]) is Equal.
// Slice must be sorted according to the order that ordering() imposes on it. This will not be checked.
// Returns None if there is no idx where ordering was Equal.
fn bsearch_first<T, F>(slice: &[T], ordering: F) -> Option<usize>
where F: Fn(&T) -> Ordering,
{
    let len = slice.len();
    if len == 0 {
        return None;
    }
    let mut start = 0;
    let mut end = len - 1;
    let mut have_answer = false;
    let mut answer : usize = 0;
    loop {
        if end < start {
            if have_answer {
                return Some(answer);
            }
            return None;
        }

        let i = start + (end - start) / 2;
        let ord = ordering(&slice[i]);

        match ord {
            Less => {
                start = i + 1;
            }
            Equal => {
                have_answer = true;
                answer = i;
                if i == 0 {
                    return Some(answer);
                }
                end = i - 1;
            }
            Greater => {
                if i == 0 {
                    return None;
                }
                end = i - 1;
            }
        }
    }
}
// Some idx of a slice for which ordering(array[idx]) is Equal. Which one exactly is undefined.
// slice must be sorted according to the order that ordering() imposes on it. This will not be checked.
// Returns None if there is no idx where ordering was Equal.
fn bsearch<T, F>(slice: &[T], ordering: F) -> Option<usize>
where F: Fn(&T) -> Ordering,
{
    let len = slice.len();
    if len == 0 {
        return None;
    }
    let mut start = 0;
    let mut end = len - 1;
    
    loop {
        if end < start {
            return None;
        }

        let i = start + (end - start) / 2;
        let ord = ordering(&slice[i]);

        match ord {
            Less => {
                start = i + 1;
            }
            Equal => {
                return Some(i);
            }
            Greater => {
                if i == 0 {
                    return None; // avoid integer underflow
                }
                end = i - 1;
            }
        }
    }
}

#[cfg(test)]
mod test_bsearch_first {
    use bsearch_first;
    fn get_vec() -> Vec<i32> {
        vec![0, 0, 0, 1, 1, 1, 3, 5, 18, 50, 71, 72 ]
    }
    #[test]
    fn zero_is_0() {
        let vec = get_vec();
        let zero_idx = bsearch_first(&vec, |t| t.cmp(&0));
        assert_eq!(zero_idx, Some(0));
    }

    #[test]
    fn seventy_two_is_11() {
        let vec = get_vec();
        let idx = bsearch_first(&vec, |t| t.cmp(&72));
        assert_eq!(idx, Some(11));
    }
    #[test]
    fn one_is_3() {
        let vec = get_vec();
        let idx = bsearch_first(&vec, |t| t.cmp(&1));
        assert_eq!(idx, Some(3));
    }
    
    #[test]
    fn one_is_2_slice() {
        let vec = get_vec();
        let idx = bsearch_first(&vec[1..], |t| t.cmp(&1));
        assert_eq!(idx, Some(2));
    }   
    
    #[test]
    fn no_13() {
        let vec = get_vec();
        let idx = bsearch_first(&vec, |t| t.cmp(&13));
        assert_eq!(idx, None);
    }

    #[test]
    fn none_for_empty() {
        let vec : Vec<i32> = vec![];
        let idx = bsearch_first(&vec, |t| t.cmp(&13));
        assert_eq!(idx, None);
    }

    #[test]
    fn big_test() {
        let width = 10;
        let multiple = 1000;
        for m in 0..multiple {
            for w in 1..width {
                let mut vec = Vec::with_capacity(w * m);
                for j in 1..m {
                    for _ in 0..w {
                        vec.push(j);
                    }
                }
                for j in 1..m {
                    let expected = (j - 1) * w;
                    match bsearch_first(&vec, |t| t.cmp(&j)) {
                        Some(actual) => { assert_eq!(actual, expected, "First idx of {} should be {}", j, expected); }
                        _ => { panic!("Didn't find first idx of {}, but there is such an idx ({})", j, expected); }
                    }
                    assert_eq!(bsearch_first(&vec, |t| t.cmp(&(m*2))), None);
                    assert_eq!(bsearch_first(&vec, |t| t.cmp(&0)), None);
                }
            }
        }
    }
}

#[cfg(test)]
mod test_bsearch {
    use bsearch;
    fn get_vec() -> Vec<i32> {
        vec![0, 0, 0, 1, 1, 1, 3, 5, 18, 50, 71, 72 ]
    }
    #[test]
    fn zero_is_first_3() {
        let vec = get_vec();
        match bsearch(&vec, |t| t.cmp(&0)) {
            Some(idx) => { assert!((0..3).contains(idx), "0 was found in 0..3"); }
            _ => { panic!("None was returned for the idx of 1, but there are such idxes (0..3)"); }
        }
    }

    #[test]
    fn seventy_two_is_11() {
        let vec = get_vec();
        let idx = bsearch(&vec, |t| t.cmp(&72));
        assert_eq!(idx, Some(11));
    }
    #[test]
    fn one_is_3_to_6() {
        let vec = get_vec();
        match bsearch(&vec, |t| t.cmp(&1)) {
            Some(idx) => { assert!((3..6).contains(idx)); },
            _ => { panic!("None was returned for the idx of 1, but there are such idxes (3..6)"); }
        }
    }
    
    #[test]
    fn one_is_2_to_5() {
        let vec = get_vec();
        match bsearch(&vec[1..], |t| t.cmp(&1)) {
            Some(idx) => {  assert!((2..5).contains(idx)); }
            _ => { panic!("None was returned for the idx of 1, but there are such idxes (2..5)"); }

        }
    }   
    
    #[test]
    fn no_13() {
        let vec = get_vec();
        let idx = bsearch(&vec, |t| t.cmp(&13));
        assert_eq!(idx, None);
    }

    #[test]
    fn none_for_empty() {
        let vec : Vec<i32> = vec![];
        let idx = bsearch(&vec, |t| t.cmp(&13));
        assert_eq!(idx, None);
    }

    #[test]
    fn big_test() {
        let width = 10;
        let multiple = 1000;
        for m in 0..multiple {
            for w in 1..width {
                let mut vec = Vec::with_capacity(w * m);
                for j in 1..m {
                    for _ in 0..w {
                        vec.push(j);
                    }
                }
                for j in 1..m {
                    let expected = ((j-1) * w)..((j-1) * w + w);
                    match bsearch(&vec, |t| t.cmp(&j)) {
                        Some(actual) => { assert!(expected.contains(actual), "Return idx should be in {:?}, but got {}.", expected, actual); }
                        _ => { panic!("Didn't find any idx of {}, but there are such idxes ({:?}).", j, expected); }
                    }
                    assert_eq!(bsearch(&vec, |t| t.cmp(&(m*2))), None);
                    assert_eq!(bsearch(&vec, |t| t.cmp(&0)), None);
                }
            }
        }

    }
}

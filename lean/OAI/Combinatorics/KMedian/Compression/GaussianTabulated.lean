import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianKernel

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

abbrev RatMatrix (r n : ℕ) := Vector (Vector ℚ n) r

def values {r n : ℕ} (A : RatMatrix r n) (i : Fin r) (j : Fin n) : ℚ :=
  A[i.val][j.val]

def tabulate {r n : ℕ} (A : Fin r → Fin n → ℚ) : RatMatrix r n :=
  Vector.ofFn (fun i => Vector.ofFn (A i))

@[simp] theorem values_tabulate {r n : ℕ} (A : Fin r → Fin n → ℚ) :
    values (tabulate A)=A := by
  funext i j
  simp only [values,tabulate,Vector.getElem_ofFn]

def kernelVector : (r n : ℕ) → RatMatrix r n → Vector ℚ n
  | 0, _, _ => Vector.ofFn (fun j => if j.val=0 then 1 else 0)
  | _+1, 0, _ => Vector.ofFn Fin.elim0
  | r+1, n+1, A =>
    let a := values A
    if h : (univ.filter (fun j => a 0 j ≠ 0)).Nonempty then
      let p := (univ.filter (fun j => a 0 j ≠ 0)).min' h
      let B := tabulate (residual a p)
      let z := kernelVector r n B
      Vector.ofFn (lift a p (fun j => z[j.val]))
    else kernelVector r (n+1) (tabulate (fun i j => a i.succ j))

theorem kernelVector_eq (r n : ℕ) (A : RatMatrix r n) :
    (fun j : Fin n => (kernelVector r n A)[j.val])=kernel r n (values A) := by
  induction r generalizing n with
  | zero => funext j; simp only [kernelVector,kernel,Vector.getElem_ofFn]
  | succ r ih =>
    cases n with
    | zero => exact funext (fun j => Fin.elim0 j)
    | succ n =>
      by_cases h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty
      · rw [kernelVector,kernel,dite_eq_left h,dite_eq_left h]
        have hh := ih n (tabulate (residual (values A) ((univ.filter (fun j => values A 0 j ≠ 0)).min' h)))
        simp only [values_tabulate] at hh
        funext j
        simp only [Vector.getElem_ofFn]
        rw [hh]
      · rw [kernelVector,kernel,dite_eq_right h,dite_eq_right h]
        have hh := ih (n+1) (tabulate (fun i j => values A i.succ j))
        simpa only [values_tabulate] using hh

end MetricKMedian.Gaussian

end OAI

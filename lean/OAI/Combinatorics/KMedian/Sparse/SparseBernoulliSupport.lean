import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSupport
import OAI.Combinatorics.KMedian.Sparse.SparseBernoulliSubsets

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem run_positive (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℕ) (a : Fin (run (d := d) p hp t).length) :
    0 < (run (d := d) p hp t).law.rational.weight a := by
  induction t with
  | zero =>
    change 0 < (SparseIntegerLaw.dirac (fun _ : Fin n => false)).law.rational.weight a
    change (0:ℚ) < 1/1
    norm_num
  | succ t ih =>
    let inv : SparseIntegerLaw (Fin n → Bool) → Prop := fun μ =>
      ∀ a : Fin μ.length, 0 < μ.law.rational.weight a
    suffices hs : inv (run (d := d) p hp (t+1)) from hs a
    rw [run]
    split_ifs with ht
    · exact ((run (d := d) p hp t).branch (fun _ => p ⟨t,ht⟩)
        (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)).compressAuto_positive _
    · exact ih

theorem single_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (i : Fin n) : (run (d := 2) p hp n).moment (fun q => flag q i)=p i := by
  simpa only [prod_singleton] using subset_moment p hp {i} (by simp : ({i} : Finset (Fin n)).card ≤ 2)

theorem pair_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (i j : Fin n) (hij : i≠j) :
    (run (d := 2) p hp n).moment (fun q => flag q i*flag q j)=p i*p j := by
  simpa only [prod_pair hij] using subset_moment p hp {i,j} (by simp [hij] : ({i,j} : Finset (Fin n)).card ≤ 2)

theorem fixed (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (a : Fin (run (d := 2) p hp n).length) (i : Fin n) (hi : p i=0 ∨ p i=1) :
    flag (run (d := 2) p hp n).states[a.val] i=p i := by
  have hm := single_moment p hp i
  rcases hi with hi | hi
  · have hh := (run (d := 2) p hp n).zero_indicator (fun q => q i=true)
      (hm.trans hi) a (run_positive p hp n a)
    simp only [flag,ite_eq_right hh,hi]
  · have hh := (run (d := 2) p hp n).one_indicator (fun q => q i=true)
      (hm.trans hi) a (run_positive p hp n a)
    simp only [flag,ite_eq_left hh,hi]

end MetricKMedian.SparseBernoulli
end
end

end OAI

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

/-! # The finite Euler-weight moment needed for fixed-shift sieving -/

namespace Ostmann

open scoped Classical BigOperators

 theorem sieve_weight_mass (P : Finset ℕ) (w : ℕ → ℝ) :
    (∑ U ∈ P.powerset, ∏ p ∈ U, w p) = ∏ p ∈ P, (1 + w p) :=
  (Finset.prod_one_add P).symm

 theorem sieve_weight_moment (P : Finset ℕ) (w L : ℕ → ℝ)
    (hw : ∀ p ∈ P, 1 + w p ≠ 0) :
    (∑ U ∈ P.powerset, (∏ p ∈ U, w p) * ∑ p ∈ U, L p) =
      (∏ p ∈ P, (1 + w p)) * ∑ p ∈ P, (w p / (1 + w p)) * L p := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hfresh (U : Finset ℕ) (hU : U ∈ P.powerset) : p ∉ U :=
      fun h => hp (Finset.mem_powerset.mp hU h)
    have hwP : ∀ q ∈ P, 1 + w q ≠ 0 := fun q hq => hw q (Finset.mem_insert_of_mem hq)
    have hwp : 1 + w p ≠ 0 := hw p (Finset.mem_insert_self _ _)
    have hsecond :
        (∑ U ∈ P.powerset, (∏ q ∈ insert p U, w q) * ∑ q ∈ insert p U, L q) =
          w p * (L p * (∏ q ∈ P, (1 + w q)) +
            ∑ U ∈ P.powerset, (∏ q ∈ U, w q) * ∑ q ∈ U, L q) := by
      calc
        _ = ∑ U ∈ P.powerset,
            w p * (L p * (∏ q ∈ U, w q) + (∏ q ∈ U, w q) * ∑ q ∈ U, L q) := by
          apply Finset.sum_congr rfl
          intro U hU
          rw [Finset.prod_insert (hfresh U hU), Finset.sum_insert (hfresh U hU)]
          ring
        _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, sieve_weight_mass]
    rw [Finset.sum_powerset_insert hp, hsecond, ih hwP, Finset.prod_insert hp,
      Finset.sum_insert hp]
    field_simp [hwp]
    ring

 theorem fixed_shift_weight_moment (P : Finset ℕ) (j : ℝ)
    (hj : 0 ≤ j) (hP : ∀ p ∈ P, j < (p : ℝ)) :
    (∑ U ∈ P.powerset, (∏ p ∈ U, j / ((p : ℝ) - j)) * ∑ p ∈ U, Real.log (p : ℝ)) =
      (∏ p ∈ P, (p : ℝ) / ((p : ℝ) - j)) *
        (j * ∑ p ∈ P, Real.log (p : ℝ) / p) := by
  have hfactor (p : ℕ) (hp : p ∈ P) : 1 + j / ((p : ℝ) - j) = (p : ℝ) / ((p : ℝ) - j) := by
    have hn : (p : ℝ) - j ≠ 0 := ne_of_gt (sub_pos.mpr (hP p hp))
    field_simp [hn]
    ring
  have hprob (p : ℕ) (hp : p ∈ P) :
      (j / ((p : ℝ) - j)) / (1 + j / ((p : ℝ) - j)) = j / p := by
    rw [hfactor p hp]
    have hn : (p : ℝ) - j ≠ 0 := ne_of_gt (sub_pos.mpr (hP p hp))
    have hnp : (p : ℝ) ≠ 0 := ne_of_gt (lt_of_le_of_lt hj (hP p hp))
    field_simp
  rw [sieve_weight_moment P _ _ (fun p hp => by
    rw [hfactor p hp]
    exact (div_pos (lt_of_le_of_lt hj (hP p hp)) (sub_pos.mpr (hP p hp))).ne')]
  rw [Finset.prod_congr rfl hfactor]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hprob p hp]
  ring

end Ostmann

end OAI

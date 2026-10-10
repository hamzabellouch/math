import Mathlib
import OAI.Probability.BinarySweep.Processes.AssignmentWeight

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

def localPathWeight {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (j : Fin b) (y : GridOutside bits j) : ℝ :=
  assignmentWeight (lineLaw (bits j) z) (lineInput H j y) (lineOutput H j y)

lemma fallingCost_formula {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) :
    fallingCost m u = (u : ℝ) * Real.log m - Real.log (m.descFactorial u : ℕ) := by
  have hmp : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdf : (m.descFactorial u : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hu).ne'
  rw [fallingCost, Real.log_div (pow_ne_zero _ hmp) hdf, Real.log_pow]

lemma assignmentWeight_eq_of_card_eq {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (p : Equiv.Perm X → ℝ) (A B : I ↪ X) (A' B' : J ↪ X) (f : I ↪ J)
    (hA : ∀ i, A' (f i) = A i) (hB : ∀ i, B' (f i) = B i)
    (hcard : Fintype.card I = Fintype.card J) : assignmentWeight p A' B' = assignmentWeight p A B := by
  have hsur : Function.Surjective f := by
    by_contra hn
    have hc := Fintype.card_lt_of_injective_not_surjective f f.injective hn
    omega
  have he (σ : Equiv.Perm X) : Assigns A' B' σ ↔ Assigns A B σ := by
    constructor
    · intro hσ i
      simpa only [hA, hB] using hσ (f i)
    · intro hσ j
      obtain ⟨i, rfl⟩ := hsur j
      simpa only [hA, hB] using hσ i
  simp only [assignmentWeight, he]

lemma assignmentWeight_log_ratio_le {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (hm : 0 < Fintype.card X) {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) (A' B' : J ↪ X) (f : I ↪ J)
    (hA : ∀ i, A' (f i) = A i) (hB : ∀ i, B' (f i) = B i) :
    Real.log (assignmentWeight p A' B' / assignmentWeight p A B) ≤
      fallingCost (Fintype.card X) (Fintype.card J) - fallingCost (Fintype.card X) (Fintype.card I) -
        ((Fintype.card J : ℝ) - Fintype.card I) * Real.log (Fintype.card X) +
          Real.log 4 * ((Fintype.card J : ℝ) - Fintype.card I) := by
  have hI := Fintype.card_le_of_injective A A.injective
  have hJ := Fintype.card_le_of_injective A' A'.injective
  have hi : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card I) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hI
  have hj : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card J) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hJ
  have wi : 0 < assignmentWeight p A B := lt_of_lt_of_le (by positivity) (assignmentWeight_comparison hl hu A B).1
  have wj : 0 < assignmentWeight p A' B' := lt_of_lt_of_le (by positivity) (assignmentWeight_comparison hl hu A' B').1
  by_cases hc : Fintype.card I = Fintype.card J
  · rw [assignmentWeight_eq_of_card_eq p A B A' B' f hA hB hc, div_self wi.ne', Real.log_one, hc]
    simp
  · have hIJ := Fintype.card_le_of_injective f f.injective
    have hgap : (1 : ℝ) ≤ (Fintype.card J : ℝ) - Fintype.card I := by
      have hh : Fintype.card I + 1 ≤ Fintype.card J := by omega
      exact_mod_cast (show (1 : ℤ) ≤ (Fintype.card J : ℤ) - Fintype.card I from by omega)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    calc
      _ ≤ Real.log (4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
          (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)) :=
        Real.log_le_log (div_pos wj wi) (assignmentWeight_ratio_le hl hu A B A' B')
      _ = Real.log 4 + Real.log (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) -
          Real.log (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ) := by
        rw [Real.log_div (by positivity) hj.ne', Real.log_mul (by norm_num) hi.ne']
      _ ≤ _ := by
        rw [fallingCost_formula hm hI, fallingCost_formula hm hJ]
        nlinarith

end BinaryCoordinateSweeps

end

end OAI

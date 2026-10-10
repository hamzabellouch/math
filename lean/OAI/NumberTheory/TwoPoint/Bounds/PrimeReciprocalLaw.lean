import OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability

namespace OAI

/-! Restore the harmonic mass after using the normalized prime law. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def primeHarmonicMass (P : Finset ℕ) : ℝ :=
  ∑ p : P, (p.val : ℝ)⁻¹

noncomputable def primeReciprocalLaw (P : Finset ℕ) (hV : 0 < primeHarmonicMass P) : FiniteLaw P where
  weight p := (p.val : ℝ)⁻¹ / primeHarmonicMass P
  nonneg p := div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hV.le
  total := by
    rw [← sum_div]
    exact div_self hV.ne'

lemma primeReciprocalLaw_atom_le (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (H : ℕ) (hH : 0 < H) (hlo : ∀ p ∈ P, H ≤ p) (p : P) :
    (primeReciprocalLaw P hV).weight p ≤ (primeHarmonicMass P * H)⁻¹ := by
  have hp : (H : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast hlo _ p.property
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ (H : ℝ)⁻¹ / primeHarmonicMass P :=
      div_le_div_of_nonneg_right (inv_anti₀ hH' hp) hV.le
    _ = _ := by rw [div_eq_mul_inv, mul_inv_rev]

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma primeReciprocalLaw_mass_product (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (x : α → P) :
    primeHarmonicMass P ^ Fintype.card α *
        (FiniteLaw.independent (fun _ : α => primeReciprocalLaw P hV)).weight x =
      ∏ z, ((x z).val : ℝ)⁻¹ := by
  change primeHarmonicMass P ^ Fintype.card α *
    (∏ z, ((x z).val : ℝ)⁻¹ / primeHarmonicMass P) = _
  rw [prod_div_distrib]
  simp only [prod_const, card_univ]
  exact mul_div_cancel₀ _ (pow_ne_zero _ hV.ne')

/-- Every abstract label keeps its reciprocal factor, even when distinct
labels receive the same numerical prime. -/
lemma primeReciprocalLaw_restore (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (E : (α → P) → Prop) :
    (∑ x : α → P, if E x then ∏ z, ((x z).val : ℝ)⁻¹ else 0) =
      primeHarmonicMass P ^ Fintype.card α *
        (FiniteLaw.independent (fun _ : α => primeReciprocalLaw P hV)).probability E := by
  classical
  simp only [FiniteLaw.probability, FiniteLaw.average, mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : E x
  · simp only [hx, ite_true, mul_one]
    exact (primeReciprocalLaw_mass_product P hV x).symm
  · simp only [hx, ite_false, mul_zero]

lemma primeReciprocalLaw_restore_bound (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (E : (α → P) → Prop) (B : ℝ)
    (hB : (FiniteLaw.independent (fun _ : α => primeReciprocalLaw P hV)).probability E ≤ B) :
    (∑ x : α → P, if E x then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      primeHarmonicMass P ^ Fintype.card α * B := by
  rw [primeReciprocalLaw_restore P hV E]
  exact mul_le_mul_of_nonneg_left hB (pow_nonneg hV.le _)

end TwoPointCorrelations

end OAI

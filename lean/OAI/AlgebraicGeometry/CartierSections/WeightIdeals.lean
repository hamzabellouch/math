import OAI.AlgebraicGeometry.CartierSections.IsolatedJets
import Mathlib.RingTheory.MvPowerSeries.Equiv

namespace OAI

/-!
# Monomial weight ideals

The monomial ideal above a weight bound is finitely generated. Its elements vanish at
all exponents below the bound, so the initial monomial does not belong to this ideal.
-/

open scoped BigOperators

namespace CartierSections

section WeightIdealProperties
variable {ι k : Type*} [Fintype ι] [Field k]

/-- The ideal of series whose coefficients vanish up to the specified weight. -/
noncomputable def weightVanishingIdeal (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (L : ℝ) :
    Ideal (MvPowerSeries ι k) where
  carrier := {f | ∀ d, realWeight w d ≤ L → MvPowerSeries.coeff d f = 0}
  zero_mem' := by intro d hd; simp
  add_mem' := by
    intro f g hf hg d hd
    simp [hf d hd, hg d hd]
  smul_mem' := by
    classical
    intro r f hf d hd
    change MvPowerSeries.coeff d (r * f) = 0
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro t ht
    have hsum : t.1 + t.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp ht
    have hwle : realWeight w t.2 ≤ realWeight w d := by
      rw [← hsum, realWeight_add]
      linarith [realWeight_nonneg hw t.1]
    rw [hf t.2 (hwle.trans hd), mul_zero]

theorem boundaryWeightIdeal_le_weightVanishingIdeal
    (B : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (L : ℝ) :
    (boundaryWeightIdeal B w L : Ideal (MvPowerSeries ι k)) ≤ weightVanishingIdeal w hw L := by
  classical
  apply Ideal.span_le.mpr
  rintro _ ⟨e, he, rfl⟩ d hd
  rw [MvPowerSeries.coeff_monomial, ite_eq_right]
  intro heq
  subst d
  exact (not_le_of_gt he.2) hd

/-- An initial monomial does not belong to the ideal of strictly higher weight. -/
theorem initial_monomial_not_mem_boundaryWeightIdeal
    (B : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (α : ι →₀ ℕ) :
    (MvPowerSeries.monomial α 1 : MvPowerSeries ι k) ∉
      boundaryWeightIdeal B w (realWeight w α) := by
  intro h
  have hc := boundaryWeightIdeal_le_weightVanishingIdeal B w hw (realWeight w α) h α le_rfl
  simp at hc

theorem boundaryWeightIdeal_fg (B : Finset ι) (w : ι → ℝ) (L : ℝ) :
    (boundaryWeightIdeal B w L : Ideal (MvPowerSeries ι k)).FG :=
  IsNoetherian.noetherian _

end WeightIdealProperties

end CartierSections

end OAI

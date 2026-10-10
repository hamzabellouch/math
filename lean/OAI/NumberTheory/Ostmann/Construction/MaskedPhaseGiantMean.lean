import OAI.NumberTheory.Ostmann.Construction.PhaseGiantCollision

namespace OAI

/-! # The favorable-prime mask in the initial giant

Nonfavorable primes remain in the prior. Their physical test is exactly zero.
-/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

@[simp] theorem phaseGiantPhysical_zero {p : ℕ} [NeZero p] (x : ZMod p) :
    phaseGiantPhysical (fun _ : ZMod p => (0 : ℂ)) x = 0 := by
  simp [phaseGiantPhysical, densityFourierInverse, densityFourier, additiveFourier_apply]

noncomputable def favorablePhaseTransform {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (F : Finset I) (i : I) : ZMod (p i) → ℂ :=
  if i ∈ F then normalizedResidueTransform (S i) else fun _ => 0

theorem favorablePhaseTransform_real {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))
    (F : Finset I) (i : I) (x : ZMod (p i)) :
    (phaseGiantPhysical (favorablePhaseTransform p S F i) x).im = 0 := by
  apply phaseGiantPhysical_real
  intro b
  by_cases hi : i ∈ F
  · simpa only [favorablePhaseTransform, ite_eq_left hi] using normalizedResidueTransform_neg (S i) b
  · simp only [favorablePhaseTransform, ite_eq_right hi, map_zero]

/-- The favorable Fourier L1 mass gives a positive uniform-support mean,
while the other primes make zero contribution. -/
theorem favorablePhase_uniform_mean_lower {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))
    (F : Finset I) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (γ : ℝ)
    (hS : ∀ i ∈ F, (S i).Nonempty) (hSp : ∀ i ∈ F, (S i).card < p i)
    (hσ : ∀ i ∈ F, residueDensity (S i) ≤ 2 / 3)
    (hγ : ∀ i ∈ F, γ ≤ (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖) :
    (γ / 2) * (∑ i ∈ F, w i) ≤
      ∑ i, w i * (((S i).card : ℝ)⁻¹ *
        ∑ x ∈ S i, (phaseGiantPhysical (favorablePhaseTransform p S F i) x).re) := by
  have hi (i : I) : (if i ∈ F then (γ / 2) * w i else 0) ≤
      w i * (((S i).card : ℝ)⁻¹ *
        ∑ x ∈ S i, (phaseGiantPhysical (favorablePhaseTransform p S F i) x).re) := by
    by_cases hmem : i ∈ F
    · simp only [ite_eq_left hmem, favorablePhaseTransform]
      have hu := phaseGiantPhysical_uniform_mean_lower (S i) (hS i hmem) (hSp i hmem) (hσ i hmem)
      have hh : γ / 2 ≤ ((S i).card : ℝ)⁻¹ *
          ∑ x ∈ S i, (phaseGiantPhysical (normalizedResidueTransform (S i)) x).re := by
        linarith [hγ i hmem]
      simpa only [mul_comm (γ / 2)] using mul_le_mul_of_nonneg_left hh (hw i)
    · simp [favorablePhaseTransform, hmem]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simpa only [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum] using hh

/-- The initial empirical mean, with the genuine Fourier phase mask, pays
only the square-root collision loss from Section 7.1. -/
theorem favorablePhase_empirical_mean_lower {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))
    (F : Finset I) (μ : ∀ i, ZMod (p i) → ℝ)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (γ B : ℝ)
    (hS : ∀ i ∈ F, (S i).Nonempty) (hSp : ∀ i ∈ F, (S i).card < p i)
    (hσ : ∀ i ∈ F, residueDensity (S i) ≤ 2 / 3)
    (hγ : ∀ i ∈ F, γ ≤ (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖)
    (hbudget : (∑ i, w i * ((p i : ℝ) *
      ∑ x ∈ S i, (μ i x - 1 / ((S i).card : ℝ)) ^ 2)) ≤ B) :
    (γ / 2) * (∑ i ∈ F, w i) - Real.sqrt (∑ i, w i) * Real.sqrt B ≤
      ∑ i, w i * ∑ x ∈ S i, μ i x *
        (phaseGiantPhysical (favorablePhaseTransform p S F i) x).re := by
  have hu := favorablePhase_uniform_mean_lower p S F w hw γ hS hSp hσ hγ
  have he := phaseGiant_weighted_empirical_mean_lower p S μ
    (favorablePhaseTransform p S F) w hw B hbudget
  linarith

end Ostmann

end OAI

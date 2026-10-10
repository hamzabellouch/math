import OAI.Geometry.RCD.Metric.RadonDensityL2Bound

namespace OAI

/-! # Weighted Hessian bounds retaining the full positive mass -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates

/-- A deliberately linear density bound, convenient for Gaussian tails. -/
theorem abs_le_factor_one_add_density {h j b : ℝ} (hj : 0 ≤ j) (hb : 0 ≤ b)
    (hh : h^2 ≤ j*b^2) : |h| ≤ b*(1+j) := by
  have hsq : h^2 ≤ (b*(1+j))^2 := by
    nlinarith only [hh,mul_nonneg (sq_nonneg b) (sq_nonneg j),sq_nonneg b,
      mul_nonneg (sq_nonneg b) hj]
  exact (sq_le_sq₀ (abs_nonneg h) (mul_nonneg hb (by positivity))).mp
    (by simpa only [sq_abs] using hsq)

/-- The weighted mixed estimate uses only the product of the two energies. -/
theorem weighted_abs_le_one_add_density {w h j e f b : ℝ}
    (hw : 0 ≤ w) (hj : 0 ≤ j) (hb : 0 ≤ b)
    (hh : h^2 ≤ j*e*f) (he : w^2*e*f ≤ b^2) :
    w*|h| ≤ b*(1+j) := by
  have hwh : (w*h)^2 ≤ j*b^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hh (sq_nonneg w)
    have h₂ := mul_le_mul_of_nonneg_left he hj
    nlinarith only [h₁,h₂]
  simpa only [abs_mul,abs_of_nonneg hw] using abs_le_factor_one_add_density hj hb hwh

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- A pointwise density estimate integrates against the complete mass,
including any singular part of the Bochner measure. -/
theorem integral_abs_le_full_mass (σ : Measure X) [IsFiniteMeasure σ]
    {S : Set X} (hS : μ S ≠ ⊤) {H : X → ℝ}
    (hH : AEStronglyMeasurable H (μ.restrict S)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ.restrict S, |H x| ≤ B*(1+(σ.rnDeriv μ x).toReal)) :
    Integrable H (μ.restrict S) ∧
      (∫ x in S, |H x| ∂μ) ≤ B*(μ.real S+σ.real S) := by
  have hJ : Integrable (fun x => (σ.rnDeriv μ x).toReal) (μ.restrict S) :=
    Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (measure_ne_top σ S)
  have hI : Integrable (fun _ : X => (1:ℝ)) (μ.restrict S) :=
    integrableOn_const hS
  have hmajor := (hI.add hJ).const_mul B
  have hi : Integrable H (μ.restrict S) := hmajor.mono' hH
    (hb.mono fun _ hx => by simpa only [Real.norm_eq_abs, Pi.add_apply] using hx)
  refine ⟨hi,?_⟩
  calc
    (∫ x in S, |H x| ∂μ) ≤ ∫ x in S, B*(1+(σ.rnDeriv μ x).toReal) ∂μ :=
      integral_mono_ae hi.abs hmajor hb
    _ = B*(μ.real S+∫ x in S, (σ.rnDeriv μ x).toReal ∂μ) := by
      rw [integral_const_mul,integral_add hI hJ,integral_const]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_right
      (Measure.setIntegral_toReal_rnDeriv_le (μ := σ) (ν := μ) (measure_ne_top σ S)) _) hB

end RegularPointCoordinates

end

end OAI

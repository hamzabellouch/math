import OAI.MeasureTheory.Falconer.Measures.ProductSchurIntegral
import OAI.MeasureTheory.Falconer.Estimates.ProfileMassError
import OAI.MeasureTheory.Falconer.Fourier.GraphKernelBounds
import OAI.MeasureTheory.Falconer.Fourier.InheritedSymbolMeasurability

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularH_uniform_bound (a v : ℝ) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0)
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal ≤
      (2:ℝ)^(2*(v-a)) * ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ)) * (4*W) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw hs
  obtain ⟨hf,he⟩ := sourceAngularH_finite_integral a v Ψ U V hU hV hC hD hbU hbV
  refine ⟨hf,?_⟩
  rw [he]
  have hb : ∀ᵐ r ∂sourceAngularShellMeasure v Ψ,
      ‖sourceRealAngularMoment U r*sourceRealAngularMoment V r‖ ≤
        (C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ) := by
    filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sourceRealAngularMoment_nonneg U r)
      (sourceRealAngularMoment_nonneg V r))]
    exact mul_le_mul (sourceRealAngularMoment_bound U hbU r) (sourceRealAngularMoment_bound V hbV r)
      (sourceRealAngularMoment_nonneg V r) (by positivity)
  have hi := (le_abs_self (∫ r, sourceRealAngularMoment U r*sourceRealAngularMoment V r
      ∂sourceAngularShellMeasure v Ψ)).trans (norm_integral_le_of_norm_le_const hb)
  have hm := sourceAngularShellMeasure_real_mass_le v Ψ hW hw hs
  calc
    _ ≤ (2:ℝ)^(2*(v-a)) *
        ((sourceAngularShellMeasure v Ψ).real univ * ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ))) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hi) (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hm
        (by positivity : 0 ≤ ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ)))
      nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ (2:ℝ)^(2*(v-a)))]

end PlanarFalconer

end OAI

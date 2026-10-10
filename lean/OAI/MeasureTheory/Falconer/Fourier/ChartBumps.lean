import OAI.MeasureTheory.Falconer.Fourier.BumpDerivatives
import OAI.MeasureTheory.Falconer.Angular.CapNet

namespace OAI

/-!
# Cap bump derivatives in every rotated spherical chart

The constants depend only on the ambient dimension and derivative order.
The cap center, rotation, radius and transverse chart coordinate remain free.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def rotatedChartCurve {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) (u : ℝ) : Space (n+2) :=
  e (gnomonicChart (coordinateJoin y u))

theorem rotatedChartCurve_contDiff {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) :
    ContDiff ℝ ∞ (rotatedChartCurve e y) := by
  have hn (u : ℝ) : (chartPole n+transverseLift y)+u•chartAxis n ≠ 0 := by
    rw [add_assoc]
    apply tangent_chart_nonzero (chartPole_norm n)
    simp only [inner_add_right,real_inner_smul_right,chartPole_inner_transverse,
      chartPole_inner_axis,mul_zero,add_zero]
  have hp := normalizedLine_contDiff (chartPole n+transverseLift y) (chartAxis n) hn
  have he : ContDiff ℝ ∞ (fun x : Space (n+2) => e x) := e.toContinuousLinearMap.contDiff
  change ContDiff ℝ ∞ (fun u => e (gnomonicChart (coordinateJoin y u)))
  simpa only [Function.comp_def,gnomonicChart_coordinateJoin] using he.comp hp

@[simp] theorem rotatedChartCurve_norm {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) (u : ℝ) :
    ‖rotatedChartCurve e y u‖ = 1 := by
  simp only [rotatedChartCurve,LinearIsometryEquiv.norm_map,sphere_norm]

theorem capBump_rotated_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  obtain ⟨D,hD,hDb⟩ := tangent_line_derivative_scale (E := Space (n+2)) m
  obtain ⟨C,hC,hCb⟩ := capBump_curve_derivatives (n+2) m
  refine ⟨C*D^m,by positivity,?_⟩
  intro δ hδ hδ1 c e y hy u hu
  have hp : ∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k (rotatedChartCurve e y) u‖ ≤ D^k := by
    intro k hk hkm
    have he : rotatedChartCurve e y = e ∘
        normalizedLine (chartPole n+transverseLift y) (chartAxis n) := by
      funext t
      simp only [rotatedChartCurve,Function.comp_def,gnomonicChart_coordinateJoin]
    rw [he,← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      e.norm_iteratedFDeriv_comp_left,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hDb _ _ _ (chartPole_norm n) (chartAxis_norm n)
      (chartPole_inner_transverse y) (chartPole_inner_axis n) (transverseLift_inner_axis y)
      (by simpa only [transverseLift_norm] using hy) u hu k hk hkm
  have hh := hCb δ hδ hδ1 c (rotatedChartCurve e y) (rotatedChartCurve_contDiff e y)
    D u hD hp
  apply hh.trans_eq
  simp only [div_eq_mul_inv,mul_pow]
  ring

theorem capBump_rotated_derivative_zero {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
    (y : Space n) (u : ℝ) (hfar : δ < ‖rotatedChartCurve e y u-(c : Space (n+2))‖)
    (m : ℕ) :
    iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u = 0 := by
  have hn : rotatedChartCurve e y u ∉ tsupport (capBump δ hδ c) := by
    rw [(capBump δ hδ c).tsupport_eq]
    exact not_le.mpr hfar
  have he := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (rotatedChartCurve_contDiff e y).continuous.continuousAt
  have hh := he.iteratedDeriv_eq m
  simpa only [Function.comp_def,Pi.zero_apply,iteratedDeriv_const,ite_self] using hh

end Falconer

end OAI

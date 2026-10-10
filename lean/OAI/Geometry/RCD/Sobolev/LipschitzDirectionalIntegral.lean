import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Directional differences of Lipschitz functions under an integrable test -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem lipschitz_directional_integrable {n : ℕ} {f ψ : Euclidean n → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) (hψ : Integrable ψ volume) (v : Euclidean n) :
    Integrable (fun x => fderiv ℝ f x v*ψ x) volume := by
  apply (hψ.norm.const_mul ((L:ℝ)*‖v‖)).mono'
    ((measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable.mul hψ.aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  simp only [Pi.mul_apply,norm_mul]
  have hh := (fderiv ℝ f x).le_opNorm v
  have hb : ‖fderiv ℝ f x‖≤(L:ℝ) := norm_fderiv_le_of_lipschitz ℝ hf
  exact mul_le_mul_of_nonneg_right (hh.trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg v))) (norm_nonneg _)

theorem lipschitz_directional_integral_limit {n : ℕ} {f ψ : Euclidean n → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) (hψ : Integrable ψ volume)
    (v : Euclidean n) (r : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ((f (x+r k • v)-f x)/r k)*ψ x) atTop
      (𝓝 (∫ x, (fderiv ℝ f x v)*ψ x)) := by
  have ht : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall hr⟩
  apply tendsto_integral_of_dominated_convergence (fun x => ((L:ℝ)*‖v‖)*‖ψ x‖)
  · intro k
    exact (((hf.continuous.comp (by fun_prop)).sub hf.continuous).div_const _).aestronglyMeasurable.mul
      hψ.aestronglyMeasurable
  · exact hψ.norm.const_mul _
  · intro k
    apply Eventually.of_forall
    intro x
    have hb := hf.dist_le_mul (x+r k • v) x
    have hdist : dist (x+r k • v) x=r k*‖v‖ := by
      simp [dist_eq_norm,norm_smul,abs_of_pos (hr k)]
    rw [Real.dist_eq,hdist] at hb
    have hd : |(f (x+r k • v)-f x)/r k|≤(L:ℝ)*‖v‖ := by
      rw [abs_div,abs_of_pos (hr k)]
      apply (div_le_iff₀ (hr k)).mpr
      nlinarith only [hb]
    rw [norm_mul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hd (norm_nonneg _)).trans_eq (by ring)
  · filter_upwards [hf.ae_differentiableAt (μ := (volume : Measure (Euclidean n)))] with x hx
    have hh := ((hx.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right.comp ht).mul_const (ψ x)
    simpa only [Function.comp_def,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh

end RegularPointCoordinates

end

end OAI

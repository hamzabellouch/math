import Mathlib
import OAI.Analysis.AffineBernstein.SphereDivergence
import OAI.Analysis.AffineBernstein.BilinearNewton
import OAI.Analysis.AffineBernstein.TensorFlux

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Weighted spherical tensor integration by parts, for the literal round measure.
All smoothness and integrability statements are derived on a neighborhood of the
compact sphere. -/
theorem integral_roundHessianContraction (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} (hT : ContDiffOn ℝ ∞ T U)
    (hr : ∀ e ∈ sphere (0 : E) 1, ∀ v, inner ℝ e v = 0 → T e e v = 0 ∧ T e v e = 0)
    (hdiv : ∀ e ∈ sphere (0 : E) 1, ∀ v, inner ℝ e v = 0 → (∑ i,
      roundTensorDerivative T e (tangentProjection e (b i)) (tangentProjection e (b i)) v) = 0)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    (∫ e : sphere (0 : E) 1, f e * roundHessianContraction b T g e ∂volume.toSphere) =
      -(∫ e : sphere (0 : E) 1, T e (tangentProjection e (gradient f e))
        (tangentProjection e (gradient g e)) ∂volume.toSphere) := by
  have hG : ContDiffOn ℝ ∞ (gradient g) U := by
    intro e he
    exact (contDiffAt_gradient (hg.contDiffAt (hU.mem_nhds he))).contDiffWithinAt
  have hW : ContDiffOn ℝ ∞ (tensorFlux b T (gradient g)) U := by
    intro e he
    exact (contDiffAt_tensorFlux b (hT.contDiffAt (hU.mem_nhds he))
      (hG.contDiffAt (hU.mem_nhds he))).contDiffWithinAt
  have he1 (e : sphere (0 : E) 1) : inner ℝ (e : E) e = 1 := by
    rw [real_inner_self_eq_norm_sq, (mem_sphere_zero_iff_norm.mp e.property)]
    norm_num
  have hpoint (e : sphere (0 : E) 1) :
      roundDivergence b (tensorFlux b T (gradient g)) e = roundHessianContraction b T g e :=
    roundDivergence_tensorFlux b
      ((hT.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))
      ((hG.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))
      (he1 e) (hr e e.property) (hdiv e e.property)
  calc
    _ = ∫ e : sphere (0 : E) 1, f e *
        roundDivergence b (tensorFlux b T (gradient g)) e ∂volume.toSphere := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun e => by
        dsimp only
        rw [hpoint e]
    _ = -(∫ e : sphere (0 : E) 1, fderiv ℝ f e
        (tensorFlux b T (gradient g) e) ∂volume.toSphere) :=
      integral_sphere_by_parts b hU hSU hf hW (fun e he =>
        tensorFlux_tangent b T (gradient g) (by
          rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp he]; norm_num))
    _ = _ := by simp_rw [fderiv_tensorFlux_scalar]

/- The exact twofold angular IBP needed by the tube Euler equation. -/
theorem integral_roundHessianContraction_comm (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} (hT : ContDiffOn ℝ ∞ T U)
    (hs : ∀ e ∈ sphere (0 : E) 1, ∀ v w, T e v w = T e w v)
    (hr : ∀ e ∈ sphere (0 : E) 1, ∀ v, inner ℝ e v = 0 → T e e v = 0 ∧ T e v e = 0)
    (hdiv : ∀ e ∈ sphere (0 : E) 1, ∀ v, inner ℝ e v = 0 → (∑ i,
      roundTensorDerivative T e (tangentProjection e (b i)) (tangentProjection e (b i)) v) = 0)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    (∫ e : sphere (0 : E) 1, f e * roundHessianContraction b T g e ∂volume.toSphere) =
      ∫ e : sphere (0 : E) 1, g e * roundHessianContraction b T f e ∂volume.toSphere := by
  rw [integral_roundHessianContraction b hU hSU hT hr hdiv hf hg,
    integral_roundHessianContraction b hU hSU hT hr hdiv hg hf]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun e => hs e e.property _ _

/- For the actual Newton/cofactor of a radial homogeneous Hessian, both tensor
hypotheses of angular integration by parts are PRODUCED, not postulated. -/
theorem integral_supportNewtonTensor_by_parts (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {H : E → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (hr : ∀ q ∈ U, ∀ v, fderiv ℝ (fderiv ℝ H) q v q = 0)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    (∫ e : sphere (0 : E) 1, f e *
      roundHessianContraction b (supportNewtonTensor b H) g e ∂volume.toSphere) =
      -(∫ e : sphere (0 : E) 1, supportNewtonTensor b H e
        (tangentProjection e (gradient f e)) (tangentProjection e (gradient g e)) ∂volume.toSphere) := by
  apply integral_roundHessianContraction b hU hSU
  · intro e he
    exact (contDiffAt_supportNewtonTensor b (hH.contDiffAt (hU.mem_nhds he))).contDiffWithinAt
  · intro e he v hv
    obtain ⟨c, hc⟩ := supportNewtonTensor_radial b
      (hH.contDiffAt (hU.mem_nhds (hSU he))) (hr e (hSU he))
    constructor
    · rw [hc, hv, mul_zero]
    · rw [supportNewtonTensor_isSymm b (hH.contDiffAt (hU.mem_nhds (hSU he))), hc, hv, mul_zero]
  · intro e he v hv
    apply supportNewtonTensor_round_divergence b hU hH hr (hSU he) _ hv
    rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp he]
    norm_num
  · exact hf
  · exact hg

end AffineBernstein
end

end OAI

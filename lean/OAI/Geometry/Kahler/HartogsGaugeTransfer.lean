import OAI.Geometry.Kahler.BaseMinorant

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

lemma gaugeLogParameter_normal (φ : Base → ℝ) (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base)
    (w : ℂ) : gaugeLogParameter φ (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w) =
      normalLogWeight (φ ∘ centeredChart r U) w := by
  funext q
  simp only [gaugeLogParameter, normalLogWeight, Function.comp_apply, Complex.sub_re]
  ring

lemma metricPotential_normalGauge (φ : Base → ℝ) (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base)
    (lam : ℝ) (w : ℂ) :
    metricPotential φ lam ∘ fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w) =
      (fun q => lam * psi (centeredChart r U q.1) + logarithmicBarrier (normalLogWeight (φ ∘ centeredChart r U) w q)) := by
  funext q
  rw [Function.comp_apply, metricPotential_fiberGauge, gaugeLogParameter_normal]

lemma normalGauge_hessian_eventually {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) (lam : ℝ) (w : ℂ)
    (hn : normalLogWeight (φ ∘ centeredChart r U) w (0,w) < 0) :
    complexHessian (metricPotential φ lam ∘ fiberGaugeMap (centeredChart r U)
        (baseGaugePolynomial (φ ∘ centeredChart r U) w)) =ᶠ[𝓝 (0,w)]
      complexHessian (normalPotential (φ ∘ centeredChart r U) lam w) := by
  rw [metricPotential_normalGauge]
  have hf := chartWeight_contDiffAt hφ hr hr1 U
  have hB : ContDiffAt ℝ 2 (logarithmicBarrier ∘ normalLogWeight (φ ∘ centeredChart r U) w) (0,w) :=
    ((logarithmicBarrier_contDiffAt hn).comp (0,w) (normalLogWeight_contDiffAt (q := (0,w)) hf w)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hp : ContDiffAt ℝ 2 (fun q : Ambient => psi q.1) (0,w) :=
    ((psi_contDiffAt zero_mem_ball).comp (0,w) contDiffAt_fst).of_le (WithTop.coe_le_coe.mpr le_top)
  have ht : ContDiffAt ℝ 2 (fun q : Ambient => psi (centeredChart r U q.1)) (0,w) :=
    (((psi_contDiffAt (centeredChart_zero_mem hr hr1 U)).comp 0
      ((centeredChart_analyticAt U (z := 0) (by simp)).contDiffAt.restrict_scalars ℝ)).comp
      (0,w) contDiffAt_fst).of_le (WithTop.coe_le_coe.mpr le_top)
  filter_upwards [hB.eventually (by norm_num), hp.eventually (by norm_num), ht.eventually (by norm_num),
    psi_chart_hessian_eventually hr hr1 U w] with q hBq hpq htq heq
  ext i j
  change complexHessian (fun q => lam*psi (centeredChart r U q.1) + (logarithmicBarrier ∘ normalLogWeight (φ ∘ centeredChart r U) w) q) q i j =
    complexHessian (fun q => lam*psi q.1 + (logarithmicBarrier ∘ normalLogWeight (φ ∘ centeredChart r U) w) q) q i j
  rw [complexHessian_add (contDiffAt_const.mul htq) hBq,
    complexHessian_add (contDiffAt_const.mul hpq) hBq,
    complexHessian_const_mul htq, complexHessian_const_mul hpq, heq]

lemma sectional_normalGauge {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    (hpsh : IsPshBase φ) {lam : ℝ} (hlam : 0 < lam)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base)
    (w : ℂ) (hp : (centeredChart r U 0,Complex.exp w) ∈ hartogs φ) (u v : Ambient) :
    sectional (complexHessian (normalPotential (φ ∘ centeredChart r U) lam w)) (0,w) u v =
      sectional (hartogsMetric φ lam) (centeredChart r U 0,Complex.exp w)
        (fderiv ℂ (fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w)) (0,w) u)
        (fderiv ℂ (fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w)) (0,w) v) := by
  let F := fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w)
  have hFc : F (0,w) = (centeredChart r U 0,Complex.exp w) := by simp [F, fiberGaugeMap, baseGaugePolynomial]
  have hFp : F (0,w) ∈ hartogs φ := hFc ▸ hp
  have hn : normalLogWeight (φ ∘ centeredChart r U) w (0,w) < 0 := by
    rw [← gaugeLogParameter_normal]
    exact gaugeLogParameter_neg hFp
  have hT := centeredChart_analyticAt (r := r) U (z := 0) (by simp)
  have hF := fiberGaugeMap_analyticAt (p := (0,w)) hT (baseGaugePolynomial_analytic (φ ∘ centeredChart r U) w (0,w))
  have hJ := jacobianMatrix_det_of_fderiv_injective
    (fderiv_fiberGaugeMap_injective (p := (0,w)) hT.differentiableAt
      (fderiv_centeredChart_zero_injective hr hr1 U) (firstGaugeJet (fun q : Ambient => (φ ∘ centeredChart r U) q.1) (0,w))
      (secondGaugeJet (fun q : Ambient => (φ ∘ centeredChart r U) q.1) (0,w)))
  have he := sectional_complexHessian_comp (metricPotential_contDiffAt hφ lam hFp) hF
    (kahler_metric_det_ne_zero (hartogsMetric_isKahler hφ hpsh hlam) hFp) hJ u v
  rw [sectional_congr (normalGauge_hessian_eventually hφ hr hr1 U lam w hn), hFc] at he
  exact he

end PinchedHartogs

end

end OAI

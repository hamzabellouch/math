import OAI.Analysis.CircleDomains.Uniformization.MetricBeltramiCoefficient

namespace OAI

/-! The metric is recovered exactly, including its positive scale, from
its bounded complex coefficient. -/
open Matrix
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma metricBeltramiCoefficient_reconstruction {A : PlanarMetric} (hA : A.PosDef) :
    let μ := metricBeltramiCoefficient A
    let d := metricBeltramiDenominator A
    A 0 0 = (d / 4) * ((1 + μ.re)^2 + μ.im^2) ∧
    A 1 1 = (d / 4) * ((1 - μ.re)^2 + μ.im^2) ∧
    A 0 1 = (d / 2) * μ.im := by
  have hsym : A 1 0 = A 0 1 := by
    have h := congrFun (congrFun hA.isHermitian.eq (0 : Fin 2)) (1 : Fin 2)
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hdet : A.det = A 0 0 * A 1 1 - (A 0 1)^2 := by
    rw [Matrix.det_fin_two, hsym]
    ring
  have hd := metricBeltramiDenominator_pos hA
  have hs : (Real.sqrt A.det)^2 = A 0 0 * A 1 1 - (A 0 1)^2 := by
    rw [Real.sq_sqrt hA.det_pos.le, hdet]
  have hr : (metricBeltramiCoefficient A).re =
      (A 0 0 - A 1 1) / metricBeltramiDenominator A := by
    simp only [metricBeltramiCoefficient, Complex.div_ofReal_re]
  have hi : (metricBeltramiCoefficient A).im =
      (2 * A 0 1) / metricBeltramiDenominator A := by
    simp only [metricBeltramiCoefficient, Complex.div_ofReal_im]
  dsimp only
  rw [hr, hi]
  constructor
  · field_simp [hd.ne']
    dsimp [metricBeltramiDenominator]
    nlinarith only [hs]
  constructor
  · field_simp [hd.ne']
    dsimp [metricBeltramiDenominator]
    nlinarith only [hs]
  · field_simp [hd.ne']

end CircleDomainRigidity

end

end OAI

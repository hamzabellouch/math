import Mathlib
import OAI.Analysis.BiholderTransport.Oscillation.ActualPlateaus
import OAI.Analysis.BiholderTransport.Regularity.ActualScaleSmallness

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace WeakMTWTransport
section ActualSmallPlateau
variable {M:Type*} [MetricSpace M] [CompactSpace M] [Nonempty M] [MeasurableSpace M]

lemma exists_actual_small_plateau {vol:Measure M} {lam cap:ℝ} {x0:M}
    (hc:(densityDualClass vol lam cap x0).Nonempty)
    (hno:¬ HasPowerUpperBound (classOscillation vol lam cap x0)) {eps:ℝ} (heps:0 < eps) :
    ∃r R bm bp:ℝ,0 < r ∧ 0 < R ∧ 0 < bm ∧ 0 < bp ∧
    ∃uv∈densityDualClass vol lam cap x0,∃x y0 y1:M,
      y0∈gapSection uv.1 uv.2 x r ∧ y1∈gapSection uv.1 uv.2 x r ∧
      (∀y∈gapSection uv.1 uv.2 x r,uv.2 y0 ≤ uv.2 y) ∧
      (∀y∈gapSection uv.1 uv.2 x r,uv.2 y ≤ uv.2 y1) ∧
      sectionOscillation uv.1 uv.2 x r=uv.2 y1-uv.2 y0 ∧ 0 < uv.2 y1-uv.2 y0 ∧
      classOscillation vol lam cap x0 R ≤ (1+eps)*(uv.2 y1-uv.2 y0) ∧
      r ≤ eps*bm ∧ bm ≤ eps*bp ∧ bp ≤ eps*R ∧
      (∀k:ℕ,k ≤ 2 → bp ≤ eps*(uv.2 y1-uv.2 y0)^k) := by
  obtain ⟨J,hJ,heJ,Hs⟩:=exists_uniform_plateau_smallness
    (abs_nonneg (Real.log (1+Metric.diam (univ:Set M)^2))) heps
  obtain ⟨A,uv,huv,x,y0,y1,hA,hy0,hy1,hlo,hhi,he,hD,hR,hlog⟩:=
    exists_actual_plateau_section hc hno (show 1 ≤ J by linarith)
  obtain ⟨hrbm,hbmbp,hbpR,hbpD⟩:=Hs A (uv.2 y1-uv.2 y0) hA hD hlog
  refine ⟨Real.exp (-(A+J)),Real.exp (-A),lowerGapScale A J,upperGapScale A J,
    Real.exp_pos _,Real.exp_pos _,Real.exp_pos _,Real.exp_pos _,uv,huv,x,y0,y1,
    hy0,hy1,hlo,hhi,he,hD,?_,hrbm,hbmbp,hbpR,hbpD⟩
  exact hR.trans (mul_le_mul_of_nonneg_right heJ hD.le)

end ActualSmallPlateau
end WeakMTWTransport

end
end

end OAI

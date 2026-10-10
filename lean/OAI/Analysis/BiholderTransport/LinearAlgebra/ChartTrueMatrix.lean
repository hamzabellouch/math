import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.FrameMetric
import OAI.Analysis.BiholderTransport.Coordinates.NormalFrameTaylor
import OAI.Analysis.BiholderTransport.Calculus.JetTranslation

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartTrueMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def chartJetMatrix (a c:M) (b q:Model n) (p:Model n →L[ℝ] ℝ)
    (A:Model n →L[ℝ] Model n →L[ℝ] ℝ) : Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  frameMetric a b+secondJetPullback p A (fderiv ℝ (movingPrefixChart a c 1 b) q)
    (fderiv ℝ (fderiv ℝ (movingPrefixChart a c 1 b)) q)

omit [Nonempty M] in
lemma chartJetMatrix_normal_identity {f:M → ℝ} {a c y:M} {b q:Model n}
    (hb:b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hq:chartFiberInverse a b q∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hy:movingPrefix a 1 b q=y) (hc:y∈(extChartAt 𝓘(ℝ,Model n) c).source)
    {r:TangentSpace 𝓘(ℝ,Model n) y} (hr:r∈injectivityDomain y)
    (hrx:riemannianExp y r=(extChartAt 𝓘(ℝ,Model n) a).symm b)
    {S:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hS:HasQuadraticExpansion (fun h=>f (riemannianExp y h)) r S)
    {p:Model n} {A:Model n →L[ℝ] Model n} (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    (hAe:HasQuadraticExpansion (fun h=>f ((extChartAt 𝓘(ℝ,Model n) c).symm
      (extChartAt 𝓘(ℝ,Model n) c y+h))) p A)
    {R:TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b) → TangentSpace 𝓘(ℝ,Model n) y}
    (hR:DifferentiableAt ℝ R (chartFiberInverse a b q)) (hR0:R (chartFiberInverse a b q)=0)
    (hRe:∀ᶠ v in 𝓝 (chartFiberInverse a b q),riemannianExp y (R v)=
      riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) v) :
    ∀d,chartJetMatrix a c b q (innerSL ℝ p) ((innerSL ℝ).comp A) d d=
      inner ℝ (S (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d)))
        (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))+
      normalHessian y r (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d))
        (fderiv ℝ R (chartFiberInverse a b q) (chartFiberInverse a b d)) := by
  let B:=chartFiberInverse a b
  have he:riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) (B q)=y:=by
    simpa only [movingPrefix_eq hb,one_smul,B,chartFiberInverse] using hy
  have H:=chart_normal_pole_frame_identity B hr hq hrx he hc hS hA hAe hR hR0 hRe
  have hg:ContDiffAt ℝ 2 (movingPrefixChart a c 1 b) q:=by
    exact ((movingPrefixChart_contDiffAt hb (hy.symm ▸ hc)).comp q
      (contDiffAt_const.prodMk contDiffAt_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heq:(fun h=>movingPrefixChart a c 1 b (q+h)-extChartAt 𝓘(ℝ,Model n) c y)=
      (fun h=>extChartAt 𝓘(ℝ,Model n) c (riemannianExp
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) (B q+B h))-extChartAt 𝓘(ℝ,Model n) c y):=by
    funext h
    simp only [movingPrefixChart,movingPrefix_eq hb,one_smul,map_add,B,chartFiberInverse]
  rw [←heq] at H
  dsimp only at H
  rw [fderiv_translate_at_zero (hg.differentiableAt (by norm_num)),
    second_fderiv_translate_at_zero hg] at H
  intro d
  rw [chartJetMatrix,add_apply,add_apply,
    frameMetric_apply hb,real_inner_self_eq_norm_sq]
  exact H d

omit [Nonempty M] in
lemma chartJetMatrix_tendsto {a c:M} {b q:ℕ → Model n} {b0 q0:Model n}
    {p:ℕ → Model n →L[ℝ] ℝ} {p0:Model n →L[ℝ] ℝ}
    {A:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ} {A0:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hb0:b0∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc:movingPrefix a 1 b0 q0∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hb:Tendsto b atTop (𝓝 b0)) (hq:Tendsto q atTop (𝓝 q0))
    (hp:Tendsto p atTop (𝓝 p0)) (hA:Tendsto A atTop (𝓝 A0)) :
    Tendsto (fun k=>chartJetMatrix a c (b k) (q k) (p k) (A k)) atTop
      (𝓝 (chartJetMatrix a c b0 q0 p0 A0)) := by
  let : NormedAddCommGroup (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  have hg:=movingPrefixChart_contDiffAt hb0 hc
  have hbx:=hb.prodMk_nhds hq
  have hD:=((ContDiffAt.partial_snd_fderiv hg).continuousAt.tendsto).comp hbx
  have hD2:=((ContDiffAt.partial_snd_fderiv_two hg).continuousAt.tendsto).comp hbx
  have hf : Tendsto (fun k=>frameMetric a (b k)) atTop (𝓝 (frameMetric a b0)) :=
    (frameMetric_continuousAt hb0).tendsto.comp hb
  have hs : Tendsto (fun k=>secondJetPullback (p k) (A k)
      (fderiv ℝ (movingPrefixChart a c 1 (b k)) (q k))
      (fderiv ℝ (fderiv ℝ (movingPrefixChart a c 1 (b k))) (q k))) atTop
      (𝓝 (secondJetPullback p0 A0 (fderiv ℝ (movingPrefixChart a c 1 b0) q0)
        (fderiv ℝ (fderiv ℝ (movingPrefixChart a c 1 b0)) q0))) :=
    secondJetPullback_tendsto hp hA hD hD2
  exact hf.add hs
end ChartTrueMatrix
end WeakMTWTransport

end
end

end OAI

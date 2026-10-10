import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.FiniteActiveGrowth
import OAI.Analysis.BiholderTransport.Regularity.SecondFderivCompLinear

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma hessianValue_zero (x : M) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    hessianValue x 0 xi = ‖xi‖^2 := by
  have hA := (hessianValue_contDiffAt (zero_mem_injectivityDomain (n := n) x) xi).continuousAt
  have hl : ContinuousAt (fun r : ℝ => r • xi) 0 := continuousAt_id.smul continuousAt_const
  have h0 : (0:ℝ) • xi = 0 := zero_smul ℝ xi
  have hc : ContinuousAt (fun r : ℝ => hessianValue x (r • xi) xi) 0 := by
    exact (show ContinuousAt (fun q => hessianValue x q xi) ((0:ℝ) • xi) by simpa using hA).comp (x := (0:ℝ)) (f := fun r : ℝ => r • xi) hl
  have he : ∀ᶠ r : ℝ in 𝓝 0, r • xi ∈ injectivityDomain x := by
    exact hl.preimage_mem_nhds ((isOpen_injectivityDomain x).mem_nhds (by simpa using zero_mem_injectivityDomain (n := n) x))
  have heq : (fun r : ℝ => hessianValue x (r • xi) xi) =ᶠ[𝓝[≠] 0] (fun _ => ‖xi‖^2) := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hr0
    exact hessianValue_contracted_radial hr0 hr
  have H := tendsto_nhds_unique_of_eventuallyEq (hc.mono_left nhdsWithin_le_nhds)
    (continuousAt_const.mono_left nhdsWithin_le_nhds) heq
  simpa only [zero_smul] using H

def movingNormal (a : M) (q : Model n × Model n) : M :=
  let z := (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).symm q
  riemannianExp z.1 z.2

lemma movingNormal_contMDiffAt {a : M} {q : Model n × Model n}
    (hq : q.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,Model n × Model n) 𝓘(ℝ,Model n) ∞ (movingNormal a) q := by
  have hT : q ∈ (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).target :=
    (tangent_chart_target_iff _ q).mpr hq
  exact (contMDiff_riemannianExp (n := n) (M := M) _).comp q ((contMDiffOn_extChartAt_symm _).contMDiffAt ((isOpen_extChartAt_target _).mem_nhds hT))

section
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
lemma movingNormal_eq {a : M} {b : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target) (h : Model n) :
    movingNormal a (b,h) = riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b)
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) h) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  have hx : x ∈ (chartAt (Model n) a).source := by
    simpa only [x,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  change riemannianExp x (tangentCoordChange 𝓘(ℝ,Model n) a x x h) = _
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

lemma movingNormal_zero {a : M} {b : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target) :
    movingNormal a (b,0) = (extChartAt 𝓘(ℝ,Model n) a).symm b := by
  rw [movingNormal_eq hb,map_zero,riemannianExp_zero]

def movingNormalCost (a : M) (b p h : Model n) : ℝ :=
  cost (movingNormal a (b,h)) (movingNormal a (b,p))

lemma movingNormalCost_eq {a : M} {b : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target) (p h : Model n) :
    movingNormalCost a b p h =
      normalCost ((extChartAt 𝓘(ℝ,Model n) a).symm b)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) h) := by
  simp only [movingNormalCost,movingNormal_eq hb,normalCost]

end

lemma movingNormalCost_contDiffAt {a : M} {b p : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ContDiffAt ℝ ∞ (fun q : (Model n × Model n) × Model n =>
      movingNormalCost a q.1.1 q.1.2 q.2) ((b,p),0) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  have hA : ContMDiffAt 𝓘(ℝ,(Model n × Model n) × Model n) 𝓘(ℝ,Model n) ∞
      (fun q : (Model n × Model n) × Model n => movingNormal a (q.1.1,q.2)) ((b,p),0) :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp ((b,p),0)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,(Model n × Model n) × Model n) 𝓘(ℝ,Model n) ∞
      (fun q : (Model n × Model n) × Model n => movingNormal a (q.1.1,q.1.2)) ((b,p),0) :=
    (movingNormal_contMDiffAt (q := (b,p)) hb).comp ((b,p),0) contDiffAt_fst.contMDiffAt
  have hC : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (movingNormal a (b,0),movingNormal a (b,p)) := by
    rw [movingNormal_zero hb,movingNormal_eq hb]
    exact cost_contMDiffAt_of_injectivityDomain ⟨x,L p⟩ hp
  exact ((hC.comp ((b,p),0) (hA.prodMk hB)).contDiffAt)

lemma movingNormalCost_hasFDerivAt_zero {a : M} {b p : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    HasFDerivAt (movingNormalCost a b p)
      ((innerSL ℝ (-((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p))).comp
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b))) 0 := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  have he : movingNormalCost a b p = (fun h => normalCost x (L p) (L h)) := by
    funext h
    exact movingNormalCost_eq hb p h
  rw [he]
  exact (show HasFDerivAt (normalCost x (L p)) (innerSL ℝ (-L p)) (L 0) by
    simpa only [map_zero] using normalCost_hasFDerivAt_zero hp).comp 0 L.hasFDerivAt

lemma movingNormalCost_second {a : M} {b p : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) (v : Model n) :
    fderiv ℝ (fderiv ℝ (movingNormalCost a b p)) 0 v v =
      hessianValue ((extChartAt 𝓘(ℝ,Model n) a).symm b)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) v) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  have he : movingNormalCost a b p = (fun h => normalCost x (L p) (L h)) := by
    funext h
    exact movingNormalCost_eq hb p h
  rw [he, second_fderiv_comp_linear_zero
    ((normalCost_contDiffAt hp).of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)), hessianValue_eq_normalHessian hp]
  rfl

end WeakMTWTransport

end

end OAI

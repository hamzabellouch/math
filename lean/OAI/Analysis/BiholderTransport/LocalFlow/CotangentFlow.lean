import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ChartGradientMap

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

abbrev Phase (n:ℕ) := Model n × (Model n →L[ℝ] ℝ)

def phaseRaise (a:M) (q:Phase n) : Model n × Model n :=
  (q.1,(riemannianCoordinateMetric a q.1).inverse q.2)

def phaseLower (a:M) (q:Model n × Model n) : Phase n :=
  (q.1,riemannianCoordinateMetric a q.1 q.2)

def coordinatePhaseFlow (a:M) (q:ℝ×Phase n) : Phase n :=
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  phaseLower a (χ (sprayFlow (-q.1) (χ.symm (phaseRaise a q.2))))

omit [CompactSpace M] [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma phaseLower_contDiffAt {a:M} {q:Model n × Model n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (phaseLower a) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  exact contDiffAt_fst.prodMk ((hg.comp q contDiffAt_fst).clm_apply contDiffAt_snd)

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma phaseLower_raise {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) : phaseLower a (phaseRaise a q)=q := by
  exact Prod.ext rfl ((riemannianCoordinateMetric_isInvertible hq).self_apply_inverse q.2)

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinatePhaseFlow_zero {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) : coordinatePhaseFlow a (0,q)=q := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have ht:phaseRaise a q∈χ.target := (tangent_chart_target_iff _ _).mpr hq
  dsimp only [coordinatePhaseFlow]
  rw [neg_zero,sprayFlow_zero,χ.right_inv ht]
  exact phaseLower_raise hq

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinatePhaseFlow_contDiffAt {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (coordinatePhaseFlow a) (0,q) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have ht:phaseRaise a q∈χ.target := (tangent_chart_target_iff _ _).mpr hq
  have hi := (contMDiffOn_extChartAt_symm (n := ∞) (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)).contMDiffAt
    ((isOpen_extChartAt_target _).mem_nhds ht)
  have hr:ContDiffAt ℝ ∞ (phaseRaise a) q := coordinateRaise_contDiffAt hq
  have hinput := hi.comp (f:=fun p:ℝ×Phase n=>phaseRaise a p.2) (0,q)
    (hr.comp (0,q) contDiffAt_snd).contMDiffAt
  have hf := contMDiff_sprayFlow.contMDiffAt.comp (f:=fun p:ℝ×Phase n=>
    (-p.1,χ.symm (phaseRaise a p.2))) (0,q)
    (contDiffAt_fst.neg.contMDiffAt.prodMk hinput)
  have he:sprayFlow (-(0:ℝ)) (χ.symm (phaseRaise a q))=χ.symm (phaseRaise a q) := by
    rw [neg_zero,sprayFlow_zero]
  have hc:ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      𝓘(ℝ,Model n × Model n) ∞ χ (sprayFlow (-(0:ℝ)) (χ.symm (phaseRaise a q))) := by
    rw [he]
    exact contMDiffAt_extChartAt' (by simpa only [χ,extChartAt_source] using χ.map_target ht)
  have hout := (hc.comp (f:=fun p:ℝ×Phase n=>
    sprayFlow (-p.1) (χ.symm (phaseRaise a p.2))) (0,q) hf).contDiffAt
  have hbase:(χ (sprayFlow (-(0:ℝ)) (χ.symm (phaseRaise a q)))).1∈
      (extChartAt 𝓘(ℝ,Model n) a).target := by
    rw [he,χ.right_inv ht]; exact hq
  exact (phaseLower_contDiffAt hbase).comp (0,q) hout

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma coordinatePhaseFlow_derivative_limit {a:M} {q:Phase n}
    (hq:q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    Tendsto (fun p:ℝ×Phase n=>fderiv ℝ (fun v=>coordinatePhaseFlow a (p.1,v)) p.2)
      (𝓝 (0,q)) (𝓝 (ContinuousLinearMap.id ℝ (Phase n))) := by
  have hd := ContDiffAt.partial_snd_fderiv (f:=fun t v=>coordinatePhaseFlow a (t,v)) (coordinatePhaseFlow_contDiffAt hq)
  have he:(fun v:Phase n=>coordinatePhaseFlow a (0,v))=ᶠ[𝓝 q] id := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a).mem_nhds hq)] with v hv
    exact coordinatePhaseFlow_zero hv
  have hev:fderiv ℝ (fun v=>coordinatePhaseFlow a (0,v)) q=ContinuousLinearMap.id ℝ (Phase n) := by
    rw [he.fderiv_eq,fderiv_id]
  simpa only [hev] using hd.continuousAt.tendsto

end WeakMTWTransport

end

end OAI

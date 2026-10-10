import Mathlib
import OAI.Analysis.SymmetricDomains.AffineProductCoordinates
import OAI.Analysis.SymmetricDomains.ForwardBackwardGerm

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem exists_local_chart (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (hcut : s.HasCutoffs) (hq : q x ∈ V)
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (q x), F (G y)=y) :
    ∃ s' : NashBoundaryScalingChart c x,
      s'.tangentDim=s.tangentDim ∧ s'.normalDim=s.normalDim ∧ s'.HasCutoffs ∧
      ∃ Ω : Set (Affine N), Ω ⊆ V ∧ IsOpen ((Subtype.val : V → Affine N) ⁻¹' Ω) ∧ q x ∈ Ω ∧
        MapsTo s'.forward s'.offsets.source Ω ∧ MapsTo s'.backward Ω s'.offsets.source ∧
        (∀ y ∈ Ω, s'.forward (s'.backward y)=y) := by
  have he := s.forward_backward_germ hgood F G hF0 hF hG hGF hFG
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨W,hWsub,hWo,hpW⟩ := _root_.mem_nhds_iff.mp he
  have hf : ContinuousAt s.forward 0 :=
    (s.forward_analytic hcut 0 s.source_zero).continuousAt
  have heW : ∀ᶠ z in 𝓝 (0 : Affine s.tangentDim × Affine s.normalDim), s.forward z ∈ W := by
    apply hf.preimage_mem_nhds
    rw [s.forward_zero hgood]
    exact hWo.mem_nhds hpW
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp heW
  let e := s.offsets.restr (ball 0 r)
  have he0 : (0 : Affine s.tangentDim × Affine s.normalDim) ∈ e.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_ball]
    exact ⟨s.source_zero,mem_ball_self hr⟩
  let s' : NashBoundaryScalingChart c x := {s with offsets := e, source_zero := he0}
  have hs's : s'.offsets.source ⊆ s.offsets.source := by
    intro z hz
    exact (show z ∈ s.offsets.source ∩ ball 0 r from by
      simpa only [s',e,OpenPartialHomeomorph.restr_source' _ _ isOpen_ball] using hz).1
  have hcut' : s'.HasCutoffs := fun z hz => hcut z (hs's hz)
  have hsW : MapsTo s'.forward s'.offsets.source W := by
    intro z hz
    exact hrW (show z ∈ ball 0 r from (show z ∈ s.offsets.source ∩ ball 0 r from by
      simpa only [s',e,OpenPartialHomeomorph.restr_source' _ _ isOpen_ball] using hz).2)
  let Ω := V ∩ W ∩ s'.backward ⁻¹' s'.offsets.source
  have hΩV : Ω ⊆ V := fun _ hy => hy.1.1
  have hΩo : IsOpen ((Subtype.val : V → Affine N) ⁻¹' Ω) := by
    have hh : (Subtype.val : V → Affine N) ⁻¹' Ω =
        (Subtype.val : V → Affine N) ⁻¹' W ∩
        (fun y : V => s'.backward y.val) ⁻¹' s'.offsets.source := by
      ext y; simp only [Ω,mem_preimage,mem_inter_iff,y.property,true_and]
    rw [hh]
    exact (hWo.preimage continuous_subtype_val).inter
      (s'.offsets.open_source.preimage ((s'.backward_analytic.continuous).comp continuous_subtype_val))
  refine ⟨s',rfl,rfl,hcut',Ω,hΩV,hΩo,?_,?_,fun _ hy => hy.2,?_⟩
  · exact ⟨⟨hq,hpW⟩,by change s'.backward (q x) ∈ s'.offsets.source; rw [s'.backward_center hgood]; exact s'.source_zero⟩
  · intro z hz
    exact ⟨⟨s'.forward_mem_variety hcut' hz,hsW hz⟩,by change s'.backward (s'.forward z) ∈ s'.offsets.source; rw [s'.backward_forward hcut' hz]; exact hz⟩
  · intro y hy
    exact hWsub hy.1.2 hy.1.1

noncomputable def local_biholomorph (s : NashBoundaryScalingChart c x)
    (hcut : s.HasCutoffs) (Ω : Set (Affine N))
    (hfΩ : MapsTo s.forward s.offsets.source Ω)
    (hgS : MapsTo s.backward Ω s.offsets.source)
    (hfg : ∀ y ∈ Ω, s.forward (s.backward y)=y) :
    Biholomorph (U ∩ Ω)
      ((affineProductCoordinates s.tangentDim s.normalDim) '' s.domain 1) := by
  let e := affineProductCoordinates s.tangentDim s.normalDim
  let f : Affine N → Affine (s.tangentDim+s.normalDim) := fun y => e (s.backward y)
  let g : Affine (s.tangentDim+s.normalDim) → Affine N := fun z => s.forward (e.symm z)
  have hdom : ∀ z, z ∈ s.domain 1 ↔ z ∈ s.offsets.source ∧ s.forward z ∈ U := by
    intro z
    simp only [domain,weightedScale,Real.sqrt_one,one_smul,Prod.mk.eta,mem_ofPred_eq]
  have hfgD : ∀ y ∈ U ∩ Ω, f y ∈ e '' s.domain 1 := by
    intro y hy
    refine ⟨s.backward y, (hdom _).mpr ⟨hgS hy.2,?_⟩,rfl⟩
    rw [hfg y hy.2]
    exact hy.1
  have hgfU : MapsTo g (e '' s.domain 1) (U ∩ Ω) := by
    rintro _ ⟨z,hz,rfl⟩
    change s.forward (e.symm (e z)) ∈ _
    rw [e.symm_apply_apply]
    exact ⟨((hdom z).mp hz).2,hfΩ ((hdom z).mp hz).1⟩
  refine biholomorphOfAmbientInverse _ _ f g ?_ ?_ hfgD hgfU ?_ ?_
  · intro y _
    exact (e.toContinuousLinearMap.analyticAt _).comp (s.backward_analytic y (mem_univ _))
  · rintro _ ⟨z,hz,rfl⟩
    have ha := s.forward_analytic hcut z ((hdom z).mp hz).1
    have ha' : AnalyticAt ℂ s.forward (e.symm (e z)) := by simpa only [e.symm_apply_apply] using ha
    exact ha'.comp (e.symm.toContinuousLinearMap.analyticAt _)
  · intro y hy
    change s.forward (e.symm (e (s.backward y)))=y
    rw [e.symm_apply_apply]
    exact hfg y hy.2
  · rintro _ ⟨z,hz,rfl⟩
    change e (s.backward (s.forward (e.symm (e z))))=e z
    rw [e.symm_apply_apply,s.backward_forward hcut ((hdom z).mp hz).1]
end NashBoundaryScalingChart
end Release061

end

end OAI

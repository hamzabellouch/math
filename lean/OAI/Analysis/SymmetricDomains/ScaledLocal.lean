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

section
open Set Filter Topology
open scoped Classical
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma weightedScale_analytic (t : ℝ) (x : E × F) : AnalyticAt ℂ (weightedScale t) x := by
  change AnalyticAt ℂ (fun z : E × F => (Real.sqrt t • z.1,t • z.2)) x
  exact (analyticAt_fst.const_smul (c := Real.sqrt t)).prod
    (analyticAt_snd.const_smul (c := t))

lemma weightedUnscale_analytic (t : ℝ) (x : E × F) : AnalyticAt ℂ (weightedUnscale t) x := by
  change AnalyticAt ℂ (fun z : E × F => ((Real.sqrt t)⁻¹ • z.1,t⁻¹ • z.2)) x
  exact (analyticAt_fst.const_smul (c := (Real.sqrt t)⁻¹)).prod
    (analyticAt_snd.const_smul (c := t⁻¹))

noncomputable def weightedBiholomorph {r k : ℕ} (D : Set (Affine r × Affine k))
    {t : ℝ} (ht : 0 < t) :
    Biholomorph ((affineProductCoordinates r k) '' D)
      ((affineProductCoordinates r k) '' (weightedScale t ⁻¹' D)) := by
  let e := affineProductCoordinates r k
  let f := fun z => e (weightedUnscale t (e.symm z))
  let g := fun z => e (weightedScale t (e.symm z))
  refine biholomorphOfAmbientInverse _ _ f g ?_ ?_ ?_ ?_ ?_ ?_
  · intro z _
    exact (e.toContinuousLinearMap.analyticAt _).comp
      ((weightedUnscale_analytic t _).comp (e.symm.toContinuousLinearMap.analyticAt _))
  · intro z _
    exact (e.toContinuousLinearMap.analyticAt _).comp
      ((weightedScale_analytic t _).comp (e.symm.toContinuousLinearMap.analyticAt _))
  · rintro _ ⟨z,hz,rfl⟩
    refine ⟨weightedUnscale t z,?_,?_⟩
    · change weightedScale t (weightedUnscale t z) ∈ D
      rwa [weightedScale_unscale ht]
    · simp only [f,e,ContinuousLinearEquiv.symm_apply_apply]
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨weightedScale t z,hz,by simp only [g,e,ContinuousLinearEquiv.symm_apply_apply]⟩
  · intro z _
    simp only [f,g,e.symm_apply_apply,weightedScale_unscale ht,e.apply_symm_apply]
  · intro z _
    simp only [f,g,e.symm_apply_apply,weightedUnscale_scale ht,e.apply_symm_apply]
end

open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

lemma domain_open (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U)) (t : ℝ) : IsOpen (s.domain t) := by
  let f : s.offsets.source → V := fun z => ⟨s.forward z,s.forward_mem_variety hcut z.property⟩
  have hf : Continuous f := ((continuousOn_iff_continuous_domRestrict.mp
    (s.forward_analytic hcut).continuousOn)).subtype_mk _
  have ho := (s.offsets.open_source.isOpenMap_subtype_val) _ (hU.preimage hf)
  have he : (Subtype.val : s.offsets.source → Affine s.tangentDim × Affine s.normalDim) ''
      (f ⁻¹' ((Subtype.val : V → Affine N) ⁻¹' U)) =
      {z | z ∈ s.offsets.source ∧ s.forward z ∈ U} := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨y.property,hy⟩
    · rintro ⟨hz,hy⟩; exact ⟨⟨z,hz⟩,hy,rfl⟩
  rw [he] at ho
  exact ho.preimage (continuous_iff_continuousAt.mpr fun z => (weightedScale_analytic t z).continuousAt)

noncomputable def scaled_local_biholomorph (s : NashBoundaryScalingChart c x)
    (hcut : s.HasCutoffs) (Ω : Set (Affine N))
    (hfΩ : MapsTo s.forward s.offsets.source Ω)
    (hgS : MapsTo s.backward Ω s.offsets.source)
    (hfg : ∀ y ∈ Ω, s.forward (s.backward y)=y) {t : ℝ} (ht : 0 < t) :
    Biholomorph (U ∩ Ω)
      ((affineProductCoordinates s.tangentDim s.normalDim) '' s.domain t) := by
  let e := affineProductCoordinates s.tangentDim s.normalDim
  let f : Affine N → Affine (s.tangentDim+s.normalDim) :=
    fun y => e (weightedUnscale t (s.backward y))
  let g : Affine (s.tangentDim+s.normalDim) → Affine N :=
    fun z => s.forward (weightedScale t (e.symm z))
  have hfd : MapsTo f (U ∩ Ω) (e '' s.domain t) := by
    intro y hy
    refine ⟨weightedUnscale t (s.backward y),?_,rfl⟩
    change weightedScale t (weightedUnscale t (s.backward y)) ∈ s.offsets.source ∧ _
    rw [weightedScale_unscale ht,hfg y hy.2]
    exact ⟨hgS hy.2,hy.1⟩
  have hgu : MapsTo g (e '' s.domain t) (U ∩ Ω) := by
    rintro _ ⟨z,hz,rfl⟩
    change s.forward (weightedScale t (e.symm (e z))) ∈ _
    rw [e.symm_apply_apply]
    exact ⟨hz.2,hfΩ hz.1⟩
  refine biholomorphOfAmbientInverse _ _ f g ?_ ?_ hfd hgu ?_ ?_
  · intro y _
    exact (e.toContinuousLinearMap.analyticAt _).comp
      ((weightedUnscale_analytic t _).comp (s.backward_analytic y (mem_univ _)))
  · rintro _ ⟨z,hz,rfl⟩
    have ha := s.forward_analytic hcut (weightedScale t z) hz.1
    have ha' : AnalyticAt ℂ s.forward (weightedScale t (e.symm (e z))) := by
      simpa only [e.symm_apply_apply] using ha
    have he : AnalyticAt ℂ (fun y => e.symm y) (e z) :=
      e.symm.toContinuousLinearMap.analyticAt (e z)
    have hs : AnalyticAt ℂ (fun y => weightedScale t (e.symm y)) (e z) :=
      (weightedScale_analytic t (e.symm (e z))).comp he
    exact AnalyticAt.comp (f := fun y => weightedScale t (e.symm y)) ha' hs
  · intro y hy
    change s.forward (weightedScale t (e.symm (e (weightedUnscale t (s.backward y)))))=y
    rw [e.symm_apply_apply,weightedScale_unscale ht,hfg y hy.2]
  · rintro _ ⟨z,hz,rfl⟩
    change e (weightedUnscale t (s.backward (s.forward (weightedScale t (e.symm (e z))))))=e z
    rw [e.symm_apply_apply,s.backward_forward hcut hz.1,weightedUnscale_scale ht]

end NashBoundaryScalingChart
end Release061

end

end OAI

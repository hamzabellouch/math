import OAI.Analysis.BernoulliCone.CompactLipschitzDivergence

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation
lemma clamped_seam_axis {u v:Space 7→ℝ} {x:Space 7} (hu:U x<u x)
    (hq:Cylindrical.radiusSq axis x=0) : clampedHeight u seamHeight v x=u x := by
  have hσ:seamHeight x=0:=by rw [seamHeight_formula,hq,Real.sqrt_zero]; ring
  unfold clampedHeight
  rw [hσ,max_eq_left ((min_le_right _ _).trans ((U_nonneg x).trans hu.le))]

lemma clamped_seam_le_lower {u v:Space 7→ℝ} {x:Space 7} (hu:U x<u x)
    (hq:Cylindrical.radiusSq axis ((upperParameter x (u x))⁻¹ • x)<1) :
    clampedHeight u seamHeight v x=u x := by
  rcases (Cylindrical.radiusSq_nonneg axis x axis_norm).eq_or_lt with he|hl
  · exact clamped_seam_axis hu he.symm
  · have hs:seamHeight x≤u x:=(upperParameter_seam_iff (p:=(x,u x)) hu hl).mp hq.le
    exact max_eq_left ((min_le_right _ _).trans hs)

theorem clamped_seam_locallyLipschitz {u v:Space 7→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huU:∀y,U y<u y) :
    LocallyLipschitz (clampedHeight u seamHeight v) := by
  intro x
  rcases (Cylindrical.radiusSq_nonneg axis x axis_norm).eq_or_lt with he|hl
  · have hpx:(x,u x)∈{p:Space 7×ℝ|U p.1<p.2 ∧
        Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)<1}:=by
      refine ⟨huU x,?_⟩
      rw [Cylindrical.radiusSq_smul,←he,mul_zero]
      norm_num
    have hn:∀ᶠ y in 𝓝 x,Cylindrical.radiusSq axis ((upperParameter y (u y))⁻¹ • y)<1:=
      ((continuousAt_id.prodMk hu.continuous.continuousAt).eventually (capTube_isOpen.mem_nhds hpx)).mono fun _ h=>h.2
    obtain ⟨K,V,hV,hL⟩:=hu x
    refine ⟨K,V∩{y|clampedHeight u seamHeight v y=u y},inter_mem hV (hn.mono fun y hy=>clamped_seam_le_lower (huU y) hy),?_⟩
    intro y hy z hz
    rw [hy.2,hz.2]
    exact hL hy.1 hz.1
  · obtain ⟨σ,hσ,hσe⟩:=seamHeight_smooth_germ hl
    have hw:LocallyLipschitz (clampedHeight u σ v):=hu.max (hv.min hσ.locallyLipschitz)
    obtain ⟨K,V,hV,hL⟩:=hw x
    refine ⟨K,V∩{y|σ y=seamHeight y},inter_mem hV hσe,?_⟩
    intro y hy z hz
    have he1:clampedHeight u seamHeight v y=clampedHeight u σ v y:=by
      change max (u y) (min (v y) (seamHeight y))=max (u y) (min (v y) (σ y))
      rw [hy.2]
    have he2:clampedHeight u seamHeight v z=clampedHeight u σ v z:=by
      change max (u z) (min (v z) (seamHeight z))=max (u z) (min (v z) (σ z))
      rw [hz.2]
    rw [he1,he2]
    exact hL hy.1 hz.1

lemma clamped_sub_lower_compact {u v:Space 7→ℝ} (h:HasCompactSupport (fun x=>v x-u x)) :
    HasCompactSupport (fun x=>clampedHeight u seamHeight v x-u x) := by
  apply HasCompactSupport.intro h
  intro x hx
  have hvu:v x=u x:=sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f:=fun y=>v y-u y) hx)
  change max (u x) (min (v x) (seamHeight x))-u x=0
  rw [hvu,max_eq_left (min_le_left _ _),sub_self]

theorem clamped_seam_lipschitz {u v:Space 7→ℝ} {K L:ℝ≥0}
    (hu:LipschitzWith K u) (hv:LipschitzWith L v) (huU:∀y,U y<u y)
    (hc:HasCompactSupport (fun x=>v x-u x)) :
    ∃M:ℝ≥0,LipschitzWith M (clampedHeight u seamHeight v) := by
  have hh:=clamped_seam_locallyLipschitz hu.locallyLipschitz hv.locallyLipschitz huU
  obtain ⟨C,hC⟩:=locallyLipschitz_compact_lipschitz (hh.sub hu.locallyLipschitz) (clamped_sub_lower_compact hc)
  refine ⟨C+K,?_⟩
  convert! hC.add hu using 1
  ext x
  exact (sub_add_cancel _ _).symm
end Bernoulli.DeSilvaJerison

end
end

end OAI

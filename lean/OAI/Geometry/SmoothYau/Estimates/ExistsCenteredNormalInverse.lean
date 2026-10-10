import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.FamilyInverseFst
import OAI.Geometry.SmoothYau.Smoothness.NormalInverseVecNorm

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_centered_normal_inverse (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ rn > 0, ∃ r > 0,
    ∃ e : (E × (E →L[ℝ] E)) → OpenPartialHomeomorph E E,
    ∃ ψ : (E × (E →L[ℝ] E)) × E → E,
      ContDiff ℝ ∞ ψ ∧
      (∀ q, (e q : E → E) = normalJetMap q.1 q.2
        ((metricChristoffel g q.1).bilinearComp q.2 q.2)) ∧
      (∀ q, ContDiffOn ℝ ∞ (e q).symm (e q).target) ∧
      (∀ q ∈ metricFrameSet g K, Metric.closedBall (0 : E) rn ⊆ (e q).source) ∧
      (∀ q ∈ metricFrameSet g K, ψ (q,0) = 0) ∧
      (∀ q ∈ metricFrameSet g K, ∀ t ∈ Metric.ball (0 : E) r,
        q.1+t ∈ (e q).target ∧ (e q).symm (q.1+t) = ψ (q,t)) := by
  obtain ⟨e,he,hs,hi⟩ := exists_normal_family_inverse g
  obtain ⟨rn,hrn,hR⟩ := compact_normal_family_radius g hK
  have hsub : metricFrameSet g K ×ˢ Metric.closedBall (0 : E) rn ⊆ e.source := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    rw [hs]
    exact hR q hq x hx
  let L := e '' (metricFrameSet g K ×ˢ Metric.closedBall (0 : E) rn)
  have hL : IsCompact L := ((metricFrameSet_isCompact g hK).prod
    (isCompact_closedBall 0 rn)).image_of_continuousOn (e.continuousOn.mono hsub)
  have hLt : L ⊆ e.target := by
    rintro _ ⟨w,hw,rfl⟩
    exact e.map_source (hsub hw)
  obtain ⟨ψ,hψ,hEq⟩ := smooth_extension_near_compact hL e.open_target hLt hi.snd
  obtain ⟨O,hO,hLO,hOeq⟩ := mem_nhdsSet_iff_exists.mp hEq
  let shift : ((E × (E →L[ℝ] E)) × E) → ((E × (E →L[ℝ] E)) × E) :=
    fun w => (w.1,w.1.1+w.2)
  have hshift : ContDiff ℝ ∞ shift := contDiff_fst.prodMk ((contDiff_fst.fst).add contDiff_snd)
  have h₀ (q) (hq : q ∈ metricFrameSet g K) : (q,q.1) ∈ L := by
    refine ⟨(q,0),⟨hq,Metric.mem_closedBall_self hrn.le⟩,?_⟩
    rw [he]
    exact Prod.ext rfl (normalJetMap_zero _ _ _)
  let T := shift ⁻¹' (O ∩ e.target)
  have hT : IsOpen T := (hO.inter e.open_target).preimage hshift.continuous
  have hKT : metricFrameSet g K ×ˢ {(0 : E)} ⊆ T := by
    rintro ⟨q,t⟩ ⟨hq,ht⟩
    have ht0 : t = 0 := ht
    subst t
    change (q,q.1+0) ∈ O ∩ e.target
    rw [add_zero]
    exact ⟨hLO (h₀ q hq),hLt (h₀ q hq)⟩
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton hT hKT
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  have he1 : ∀ w, (e w).1 = w.1 := by intro w; rw [he]; rfl
  let eq := fiberOpenPartialHomeomorph e he1
  let ψc := ψ ∘ shift
  have heq (q : E × (E →L[ℝ] E)) : (eq q : E → E) = normalJetMap q.1 q.2
      ((metricChristoffel g q.1).bilinearComp q.2 q.2) := by
    funext x
    change (e (q,x)).2 = _
    rw [he]
    rfl
  have hnear (q) (hq : q ∈ metricFrameSet g K) (t) (ht : t ∈ Metric.ball (0 : E) r) :
      q.1+t ∈ (eq q).target ∧ (eq q).symm (q.1+t) = ψc (q,t) := by
    have hm : (q,t) ∈ T := hUV ⟨hKU hq,hrV ht⟩
    change (q,q.1+t) ∈ O ∩ e.target at hm
    exact ⟨hm.2,hOeq hm.1⟩
  refine ⟨rn,hrn,r,hr,eq,ψc,hψ.comp hshift,heq,
    (fun q => contDiffOn_fiberInverse e he1 q hi),(fun q hq x hx => hsub ⟨hq,hx⟩),?_,hnear⟩
  intro q hq
  have hh := (hnear q hq 0 (Metric.mem_ball_self hr)).2
  rw [add_zero] at hh
  have hx0 : (0 : E) ∈ (eq q).source := hsub ⟨hq,Metric.mem_closedBall_self hrn.le⟩
  have hz : eq q 0 = q.1 := by rw [heq,normalJetMap_zero]
  rw [←hh,←hz,(eq q).left_inv hx0]

end YauCounterexamples
end

end OAI

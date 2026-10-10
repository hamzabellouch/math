import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ExistsCenteredNormalInverse

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma centered_normal_inverse_fderiv (g : SmoothMetric E E)
    (q : E × (E →L[ℝ] E)) (ψ : E → E) (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ψ 0 = 0)
    (hcomp : (fun t => normalJetMap q.1 q.2
      ((metricChristoffel g q.1).bilinearComp q.2 q.2) (ψ t)) =ᶠ[𝓝 0] fun t => q.1+t) :
    q.2.comp (fderiv ℝ ψ 0) = ContinuousLinearMap.id ℝ E := by
  have hn := hasFDerivAt_normalJetMap q.1 q.2
    ((metricChristoffel g q.1).bilinearComp q.2 q.2)
    (fun v w => metricChristoffel_symm g q.1 (q.2 v) (q.2 w)) (ψ 0)
  rw [hψ0,map_zero,sub_zero] at hn
  rw [←hψ0] at hn
  have hh := hn.comp 0 ((hψ.differentiable (by simp) 0).hasFDerivAt)
  have hsum : HasFDerivAt (fun t : E => q.1+t) (ContinuousLinearMap.id ℝ E) 0 := by
    exact (hasFDerivAt_id (0 : E)).const_add q.1
  exact (hh.congr_of_eventuallyEq hcomp.symm).unique hsum

theorem centered_inverse_for_normal_charts
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) {K : Set NormalWaveSpace} (hK : IsCompact K)
    (e : NormalWaveParameter → OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (he : ∀ q, (e q : NormalWaveSpace → NormalWaveSpace) = normalJetMap q.1 q.2
      ((metricChristoffel g q.1).bilinearComp q.2 q.2))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsource : ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ < ρ → normalWaveEquiv x ∈ (e q).source) :
    ∃ r > 0, ∃ ψ : NormalWaveParameter × NormalWaveSpace → NormalWaveSpace,
      ContDiff ℝ ∞ ψ ∧ (∀ q ∈ metricFrameSet g K, ψ (q,0) = 0) ∧
      (∀ q ∈ metricFrameSet g K, q.2.comp (fderiv ℝ (fun t => ψ (q,t)) 0) =
        ContinuousLinearMap.id ℝ NormalWaveSpace) ∧
      (∀ q ∈ metricFrameSet g K, ∀ t ∈ Metric.ball (0 : NormalWaveSpace) r,
        ψ (q,t) ∈ (e q).source ∧ e q (ψ (q,t)) = q.1+t ∧
        (e q).symm (q.1+t) = ψ (q,t)) := by
  obtain ⟨rn,hrn,r0,hr0,e0,ψ,hψ,he0,hi0,hs0,hψ0,hnear⟩ := exists_centered_normal_inverse g hK
  let T := {w : NormalWaveParameter × NormalWaveSpace | ‖normalWaveEquiv.symm (ψ w)‖ < ρ}
  have hT : IsOpen T := isOpen_lt (continuous_norm.comp (normalWaveEquiv.symm.continuous.comp hψ.continuous)) continuous_const
  have hKT : metricFrameSet g K ×ˢ {(0 : NormalWaveSpace)} ⊆ T := by
    rintro ⟨q,t⟩ ⟨hq,ht⟩
    have ht0 : t = 0 := ht
    subst t
    change ‖normalWaveEquiv.symm (ψ (q,0))‖ < ρ
    rw [hψ0 q hq,map_zero,norm_zero]
    exact hρ
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton hT hKT
  obtain ⟨r1,hr1,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  have hcomp (q) (hq : q ∈ metricFrameSet g K) :
      (fun t => normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
        (ψ (q,t))) =ᶠ[𝓝 (0 : NormalWaveSpace)] fun t => q.1+t := by
    filter_upwards [Metric.ball_mem_nhds (0 : NormalWaveSpace) hr0] with t ht
    have hh := hnear q hq t ht
    rw [←he0 q,←hh.2,(e0 q).right_inv hh.1]
  refine ⟨min r0 r1,lt_min hr0 hr1,ψ,hψ,hψ0,?_,?_⟩
  · intro q hq
    exact centered_normal_inverse_fderiv g q _ (hψ.comp (contDiff_const.prodMk contDiff_id))
      (hψ0 q hq) (hcomp q hq)
  · intro q hq t ht
    have ht0 := Metric.ball_subset_ball (min_le_left r0 r1) ht
    have ht1 := Metric.ball_subset_ball (min_le_right r0 r1) ht
    have hm : (q,t) ∈ T := hUV ⟨hKU hq,hrV ht1⟩
    have hs : ψ (q,t) ∈ (e q).source := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using
        hsource q hq (normalWaveEquiv.symm (ψ (q,t))) hm
    have hi := hnear q hq t ht0
    have hf : e q (ψ (q,t)) = q.1+t := by
      rw [he q,←he0 q,←hi.2,(e0 q).right_inv hi.1]
    exact ⟨hs,hf,by rw [←hf,(e q).left_inv hs]⟩
end YauCounterexamples
end

end OAI

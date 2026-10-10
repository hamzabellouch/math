import OAI.Probability.SLE.Loewner.MappedFutureRange

namespace OAI

/-! Exact transport of the later slit complement to the centered future
slit complement. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma initialInverseChart_mem_domain (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) {w : ℂ} (hw : w∈upperHalfPlane) :
    initialInverseChart p hi h0 hH s w∈upperHalfPlane \ range (initialSubarc p s) := by
  by_cases hs : s=0
  · subst s
    simp only [initialInverseChart_zero,id_eq]
    refine ⟨hw,?_⟩
    rintro ⟨u,hu⟩
    have hw0 : w=0 := by simpa only [initialSubarc_apply,zero_mul,h0] using hu.symm
    rw [hw0] at hw
    exact (lt_irrefl (0:ℝ)) hw
  · rw [initialInverseChart,dite_eq_right hs]
    exact (initialSlitChart p hi h0 hH s hs).inverse_mapsTo hw

lemma centeredFutureArc_range_iff (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) (w : ℂ) :
    w-(initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)∈
        range (centeredFutureArc p hi h0 hH hst ht) ↔
      w∈range (mappedFutureArc p hi h0 hH hst ht) := by
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨u,sub_left_inj.mp hu⟩
  · rintro ⟨u,hu⟩
    exact ⟨u,congrArg (fun z : ℂ => z-_) hu⟩

lemma initialForward_centered_mem_domain_iff (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p s)) :
    initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)∈
      upperHalfPlane \ range (centeredFutureArc p hi h0 hH hst ht) ↔
      z∈upperHalfPlane \ range (initialSubarc p t) := by
  have hw := initialForwardChart_mem_upper p hi h0 hH s hz
  have hshift : initialForwardChart p hi h0 hH s z-
      (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)∈upperHalfPlane := by
    change 0<(_-(_ : ℂ)).im
    change 0<(initialForwardChart p hi h0 hH s z).im at hw
    simpa only [sub_im,ofReal_im,sub_zero] using hw
  simp only [Set.mem_sdiff,hshift,hz.1,true_and,
    centeredFutureArc_range_iff,initialForward_avoids_future_iff p hi h0 hH hst ht hz]

theorem initialForward_centered_bijOn (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) :
    BijOn (fun z => initialForwardChart p hi h0 hH s z-
      (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ))
      (upperHalfPlane \ range (initialSubarc p t))
      (upperHalfPlane \ range (centeredFutureArc p hi h0 hH hst ht)) := by
  have hsub : upperHalfPlane \ range (initialSubarc p t) ⊆
      upperHalfPlane \ range (initialSubarc p s) := by
    intro z hz
    exact ⟨hz.1,fun h => hz.2 (initialSubarc_range_mono p hst.le h)⟩
  refine ⟨fun z hz => (initialForward_centered_mem_domain_iff p hi h0 hH hst ht
    (hsub hz)).mpr hz,?_,?_⟩
  · intro z hz w hw he
    have hEq := congrArg (initialInverseChart p hi h0 hH s) (sub_left_inj.mp he)
    simpa only [initialInverse_forward_at p hi h0 hH s (hsub hz),
      initialInverse_forward_at p hi h0 hH s (hsub hw)] using hEq
  · intro w hw
    let U : ℝ := initialDrivingValue p hi h0 hH s (hst.trans ht)
    have hwH : w+(U:ℂ)∈upperHalfPlane := by
      change 0<(w+(U:ℂ)).im
      simpa only [add_im,ofReal_im,add_zero] using (show 0<w.im from hw.1)
    let z := initialInverseChart p hi h0 hH s (w+(U:ℂ))
    have hz := initialInverseChart_mem_domain p hi h0 hH s hwH
    have he : initialForwardChart p hi h0 hH s z-(U:ℂ)=w := by
      rw [initialForward_inverse p hi h0 hH s hwH,add_sub_cancel_right]
    refine ⟨z,?_,he⟩
    apply (initialForward_centered_mem_domain_iff p hi h0 hH hst ht hz).mp
    change initialForwardChart p hi h0 hH s z-(U:ℂ)∈
      upperHalfPlane \ range (centeredFutureArc p hi h0 hH hst ht)
    rw [he]
    exact hw

end SLEExactGauge

end

end OAI

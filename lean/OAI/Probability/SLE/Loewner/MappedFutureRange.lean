import OAI.Probability.SLE.Geometry.CenteredFutureSlit

namespace OAI

/-! The mapped future arc has exactly the expected physical segment as
its interior range. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma point_after_prefix_mem_domain (p : C(unitInterval,ℂ)) (hi : Injective p)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s v : unitInterval} (hsv : s<v) : p v∈upperHalfPlane \ range (initialSubarc p s) := by
  refine ⟨hH v (ne_of_gt (lt_of_le_of_lt bot_le hsv)),?_⟩
  rw [initialSubarc_range]
  rintro ⟨u,hu,he⟩
  exact (not_le_of_gt hsv) (hi he ▸ hu.2)

lemma mappedFutureArc_segment (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1)
    {u : unitInterval} (hu : u≠0) :
    mappedFutureArc p hi h0 hH hst ht u=
      initialForwardChart p hi h0 hH s (p (slitSegmentParameter s t hst.le u)) := by
  rw [mappedFutureArc_of_ne_zero p hi h0 hH hst ht hu]
  unfold mappedFutureRaw
  rw [slitSegmentParameter_eq_future hst ht hu]

theorem mappedFutureArc_range_upper (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1)
    {w : ℂ} (hw : w∈upperHalfPlane) :
    w∈range (mappedFutureArc p hi h0 hH hst ht) ↔
      ∃ v∈Ioc s t, initialForwardChart p hi h0 hH s (p v)=w := by
  constructor
  · rintro ⟨u,hu⟩
    have hu0 : u≠0 := by
      intro he
      subst u
      rw [mappedFutureArc_zero] at hu
      rw [← hu] at hw
      change 0<(_ : ℂ).im at hw
      simp only [ofReal_im,lt_self_iff_false] at hw
    exact ⟨slitSegmentParameter s t hst.le u,
      ⟨slitSegmentParameter_gt hst hu0,slitSegmentParameter_le s t hst.le u⟩,
      (mappedFutureArc_segment p hi h0 hH hst ht hu0).symm.trans hu⟩
  · rintro ⟨v,hv,he⟩
    obtain ⟨u,hu,hparam⟩ := exists_slitSegmentParameter hst hv
    refine ⟨u,?_⟩
    rw [mappedFutureArc_segment p hi h0 hH hst ht hu,hparam]
    exact he

theorem initialForward_avoids_future_iff (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1)
    {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p s)) :
    initialForwardChart p hi h0 hH s z∉range (mappedFutureArc p hi h0 hH hst ht) ↔
      z∉range (initialSubarc p t) := by
  rw [mappedFutureArc_range_upper p hi h0 hH hst ht
    (initialForwardChart_mem_upper p hi h0 hH s hz)]
  constructor
  · intro hno hzt
    rw [initialSubarc_range] at hzt
    obtain ⟨v,hv,he⟩ := hzt
    have hsv : s<v := by
      by_contra hn
      apply hz.2
      rw [initialSubarc_range]
      exact ⟨v,⟨bot_le,le_of_not_gt hn⟩,he⟩
    exact hno ⟨v,⟨hsv,hv.2⟩,congrArg (initialForwardChart p hi h0 hH s) he⟩
  · rintro hno ⟨v,hv,he⟩
    have hd := point_after_prefix_mem_domain p hi hH hv.1
    have hp := congrArg (initialInverseChart p hi h0 hH s) he
    rw [initialInverse_forward_at p hi h0 hH s hd,
      initialInverse_forward_at p hi h0 hH s hz] at hp
    apply hno
    rw [initialSubarc_range]
    exact ⟨v,⟨bot_le,hv.2⟩,hp⟩

end SLEExactGauge

end

end OAI

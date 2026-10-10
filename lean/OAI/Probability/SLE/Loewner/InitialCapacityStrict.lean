import OAI.Probability.SLE.Loewner.InitialCapacityAtZero

namespace OAI

/-! Capacity strictly increases when a simple attached slit is extended. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.capacity_lt_of_domain_difference
    {p q : C(unitInterval,ℂ)} (P : SimpleSlitChart p) (Q : SimpleSlitChart q)
    (hpq : range p ⊆ range q) {z : ℂ}
    (hz : z∈upperHalfPlane \ range p) (hzq : z∈range q) :
    P.capacity<Q.capacity := by
  have hle := P.capacity_le_of_range_subset Q hpq
  apply lt_of_le_of_ne hle
  intro he
  have hdom : upperHalfPlane \ range q ⊆ upperHalfPlane \ range p :=
    fun _ hw => ⟨hw.1,fun hp => hw.2 (hpq hp)⟩
  have hm := Q.inverse_mapsTo.mono_right hdom
  have hd := P.forward_differentiable.comp Q.inverse_differentiable hm
  have hh := hydrodynamic_composition_coefficient P.coefficient Q.coefficient
    Q.inverse_normalized Q.right_inverse
  have hcoef : Tendsto (fun w : ℂ => w*(P.forward (Q.inverse w)-w))
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 0) := by
    simpa only [he,sub_self] using hh
  have hn := hydrodynamic_composition_ratio P.coefficient Q.inverse_normalized
  have heq := holomorphic_zero_hydrodynamic_mass (hd.sub differentiableOn_id)
    (fun w hw => by
      have hb := normalized_halfPlane_height hd (P.bijOn.mapsTo.comp hm) hn hw
      change 0 ≤ (P.forward (Q.inverse w)-w).im
      simpa only [Function.comp_apply,Complex.sub_im] using sub_nonneg.mpr hb) hcoef
  have hwH := P.bijOn.mapsTo hz
  have hsame : Q.inverse (P.forward z)=z := by
    apply P.bijOn.injOn (hm hwH) hz
    exact sub_eq_zero.mp (heq (P.forward z) hwH)
  exact (Q.inverse_mapsTo hwH).2 (hsame.symm ▸ hzq)

theorem initialCapacity_strictMono (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    StrictMono (initialCapacity p hi h0 hH) := by
  intro s t hst
  have ht : t≠0 := ne_of_gt (bot_le.trans_lt hst)
  by_cases hs : s=0
  · rw [hs,initialCapacity_zero]
    exact initialCapacity_pos p hi h0 hH ht
  rw [initialCapacity,dite_eq_right hs,initialCapacity,dite_eq_right ht]
  apply SimpleSlitChart.capacity_lt_of_domain_difference _ _
    (initialSubarc_range_mono p hst.le) (z := p t)
  · refine ⟨hH t ht,?_⟩
    rw [initialSubarc_range]
    rintro ⟨u,hu,he⟩
    have hut := hi he
    exact (not_le_of_gt hst) (hut ▸ hu.2)
  · rw [initialSubarc_range]
    exact mem_image_of_mem p ⟨bot_le,le_rfl⟩

end SLEExactGauge

end

end OAI

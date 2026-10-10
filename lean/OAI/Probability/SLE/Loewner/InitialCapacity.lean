import OAI.Probability.SLE.Loewner.InitialSubarc

namespace OAI

/-! A monotone positive capacity parameter on the exact initial subarcs. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

structure SimpleSlitChart (p : C(unitInterval,ℂ)) where
  forward : ℂ → ℂ
  inverse : ℂ → ℂ
  capacity : ℝ
  capacity_pos : 0<capacity
  bijOn : BijOn forward (upperHalfPlane \ range p) upperHalfPlane
  forward_differentiable : DifferentiableOn ℂ forward (upperHalfPlane \ range p)
  inverse_differentiable : DifferentiableOn ℂ inverse upperHalfPlane
  inverse_mapsTo : MapsTo inverse upperHalfPlane (upperHalfPlane \ range p)
  left_inverse : ∀ z ∈ upperHalfPlane \ range p, inverse (forward z)=z
  right_inverse : ∀ z ∈ upperHalfPlane, forward (inverse z)=z
  coefficient : Tendsto (fun z : ℂ => z*(forward z-z)) (cocompact ℂ) (𝓝 (capacity:ℂ))
  inverse_normalized : Tendsto (fun z : ℂ => inverse z/z)
    (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1)
  height_le : ∀ z ∈ upperHalfPlane \ range p, (forward z).im≤z.im

lemma exists_simpleSlitChart (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) : Nonempty (SimpleSlitChart p) := by
  obtain ⟨G,F,c,hc,hb,hdG,hdF,hm,hl,hr,hlim,hn,hh⟩ :=
    simple_slit_exists_positive_capacity_chart p hi h0 hH
  exact ⟨⟨G,F,c,hc,hb,hdG,hdF,hm,hl,hr,hlim,hn,hh⟩⟩

noncomputable def initialSlitChart (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) (ht : t ≠ 0) : SimpleSlitChart (initialSubarc p t) :=
  Classical.choice (exists_simpleSlitChart _ (initialSubarc_injective hi ht)
    (by simpa only [initialSubarc_zero] using h0) (initialSubarc_upper hH ht))

lemma SimpleSlitChart.capacity_le_of_range_subset
    {p q : C(unitInterval,ℂ)} (P : SimpleSlitChart p) (Q : SimpleSlitChart q)
    (hpq : range p ⊆ range q) : P.capacity≤Q.capacity := by
  have hdom : upperHalfPlane \ range q ⊆ upperHalfPlane \ range p := by
    intro z hz
    exact ⟨hz.1,fun hp => hz.2 (hpq hp)⟩
  exact nested_hydrodynamic_coefficient_le P.forward_differentiable P.bijOn.mapsTo
    Q.inverse_differentiable (Q.inverse_mapsTo.mono_right hdom)
    P.coefficient Q.coefficient Q.inverse_normalized Q.right_inverse

noncomputable def initialCapacity (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) (t : unitInterval) : ℝ :=
  if ht : t=0 then 0 else (initialSlitChart p hi h0 hH t ht).capacity

@[simp] lemma initialCapacity_zero (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) : initialCapacity p hi h0 hH 0=0 := by
  simp [initialCapacity]

lemma initialCapacity_pos (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : unitInterval} (ht : t ≠ 0) : 0 < initialCapacity p hi h0 hH t := by
  rw [initialCapacity,dite_eq_right ht]
  exact (initialSlitChart p hi h0 hH t ht).capacity_pos

lemma initialCapacity_nonneg (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) (t : unitInterval) :
    0 ≤ initialCapacity p hi h0 hH t := by
  by_cases ht : t=0
  · simp only [ht,initialCapacity_zero,le_refl]
  · exact (initialCapacity_pos p hi h0 hH ht).le

theorem initialCapacity_monotone (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    Monotone (initialCapacity p hi h0 hH) := by
  intro s t hst
  by_cases hs : s=0
  · rw [hs,initialCapacity_zero]
    exact initialCapacity_nonneg p hi h0 hH t
  have ht : t≠0 := by
    intro ht
    exact hs (le_antisymm (ht ▸ hst) bot_le)
  rw [initialCapacity,dite_eq_right hs,initialCapacity,dite_eq_right ht]
  exact SimpleSlitChart.capacity_le_of_range_subset _ _ (initialSubarc_range_mono p hst)

end SLEExactGauge

end

end OAI

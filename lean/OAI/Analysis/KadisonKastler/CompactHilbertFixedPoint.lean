import OAI.Analysis.KadisonKastler.CompactHilbertCenter

namespace OAI

/-! # Fixed points for compact families with an invariant Hilbert metric -/

namespace KadisonKastler

noncomputable section

variable {X E G : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_fixed_of_compact_hilbert_image
    (K : Set X) (hK : IsCompact K) (hne : K.Nonempty) (v : X → E)
    (hdist : ∀ y, LowerSemicontinuous (fun x => ‖v x - y‖ ^ 2))
    (hmid : ∀ x ∈ K, ∀ y ∈ K, ∃ z ∈ K, v z = (1 / 2 : ℝ) • (v x + v y))
    (C : ℝ) (hC : ∀ x ∈ K, ‖v x‖ ≤ C) (hfaith : Set.InjOn v K)
    (F : G → X → X) (hmap : ∀ g x, x ∈ K → F g x ∈ K)
    (honto : ∀ g y, y ∈ K → ∃ z ∈ K, F g z = y)
    (hiso : ∀ g x, x ∈ K → ∀ y, y ∈ K →
      ‖v (F g x) - v (F g y)‖ = ‖v x - v y‖) :
    ∃ x ∈ K, ∀ g, F g x = x := by
  obtain ⟨x, hx, hc⟩ := exists_unique_compact_hilbert_center K hK hne v hdist hmid C hC
  refine ⟨x, hx, ?_⟩
  intro g
  apply hfaith (hmap g x hx) hx
  apply hc (F g x) (hmap g x hx)
  intro z hz
  obtain ⟨w, hw, rfl⟩ := honto g z hz
  rw [hiso g x hx w hw]
  have hb : BddAbove (Set.range (fun y : K => ‖v x - v y‖ ^ 2)) := by
    refine ⟨(2 * C) ^ 2, ?_⟩
    rintro _ ⟨y, rfl⟩
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans (by linarith [hC x hx, hC y y.property])
  exact le_ciSup hb (⟨w, hw⟩ : K)

end

end KadisonKastler

end OAI

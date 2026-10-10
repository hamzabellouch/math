import Mathlib

namespace OAI

noncomputable section

namespace Problem340

theorem exists_compact_set_small_fiber_labels {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∃ b : s → Fin K,
      ∀ x y, b x = b y → dist (x : X) (y : X) < ε := by
  classical
  obtain ⟨t, _hts, ht, hcover⟩ := hs.finite_cover_balls (half_pos hε)
  let := ht.fintype
  have hex (x : s) : ∃ c : t, dist (x : X) (c : X) < ε / 2 := by
    have hx := hcover x.property
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    exact ⟨⟨c, hc⟩, hxc⟩
  choose c hc using hex
  refine ⟨Fintype.card t, fun x => (Fintype.equivFin t) (c x), ?_⟩
  intro x y hxy
  have heq : c x = c y := (Fintype.equivFin t).injective hxy
  have hx := hc x
  have hy := hc y
  rw [← heq, dist_comm (y : X) (c x : X)] at hy
  have htriangle := dist_triangle (x : X) (c x : X) (y : X)
  linarith

theorem exists_small_fiber_labels {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∃ b : X → Fin K, ∀ x y, b x = b y → dist x y < ε := by
  obtain ⟨K, b, hb⟩ := exists_compact_set_small_fiber_labels
    (s := (Set.univ : Set X)) isCompact_univ hε
  exact ⟨K, fun x => b ⟨x, Set.mem_univ x⟩,
    fun x y hxy => hb ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩ hxy⟩

theorem exists_pos_small_fiber_labels {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [Nonempty X] {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∃ b : X → Fin K, ∀ x y, b x = b y → dist x y < ε := by
  obtain ⟨K, b, hb⟩ := exists_small_fiber_labels (X := X) hε
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨K, Nat.zero_lt_of_lt (b x).isLt, b, hb⟩

end Problem340

end

end OAI

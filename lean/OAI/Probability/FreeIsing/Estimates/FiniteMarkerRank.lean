import Mathlib

namespace OAI

noncomputable section

namespace Problem367.FiniteMarkerRank

variable {α β : Type*}

def rank (S : Finset α) (m : α → ℝ) (v : α) : ℕ := by
  classical
  exact (S.filter (fun w => m w < m v)).card

theorem rank_lt_of_marker_lt (S : Finset α) (m : α → ℝ)
    {u v : α} (hu : u ∈ S) (huv : m u < m v) :
    rank S m u < rank S m v := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro w hw
    obtain ⟨hwS, hwu⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwS, hwu.trans huv⟩
  · intro heq
    have hv : u ∈ S.filter (fun w => m w < m v) :=
      Finset.mem_filter.mpr ⟨hu, huv⟩
    rw [← heq] at hv
    exact (lt_irrefl (m u)) (Finset.mem_filter.mp hv).2

theorem rank_injOn (S : Finset α) (m : α → ℝ)
    (hm : Set.InjOn m (↑S : Set α)) :
    Set.InjOn (rank S m) (↑S : Set α) := by
  intro u hu v hv heq
  apply hm hu hv
  apply le_antisymm
  · by_contra h
    have hlt := rank_lt_of_marker_lt S m hv (lt_of_not_ge h)
    omega
  · by_contra h
    have hlt := rank_lt_of_marker_lt S m hu (lt_of_not_ge h)
    omega

theorem rank_lt_card (S : Finset α) (m : α → ℝ) {v : α} (hv : v ∈ S) :
    rank S m v < S.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hmem : v ∈ S.filter (fun w => m w < m v) := by rwa [heq]
  exact (lt_irrefl (m v)) (Finset.mem_filter.mp hmem).2

theorem rank_image [DecidableEq β] (S : Finset α) (e : α ≃ β) (m : β → ℝ) (v : α) :
    rank (S.image e) m (e v) = rank S (fun w => m (e w)) v := by
  classical
  unfold rank
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ e.injective

theorem rank_congr (S : Finset α) {m n : α → ℝ} {u v : α}
    (hS : ∀ w ∈ S, m w = n w) (huv : m u = n v) :
    rank S m u = rank S n v := by
  classical
  unfold rank
  congr 1
  apply Finset.filter_congr
  intro w hw
  rw [hS w hw, huv]

theorem measurable_rank (S : Finset α) (v : α) :
    Measurable (fun m : α → ℝ => rank S m v) := by
  classical
  have heq : (fun m : α → ℝ => rank S m v) =
      (fun m => ∑ w ∈ S, if m w < m v then (1 : ℕ) else 0) := by
    funext m
    simp [rank]
  rw [heq]
  apply Finset.measurable_sum
  intro w hw
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply w)
    (measurable_pi_apply v)) measurable_const measurable_const

end Problem367.FiniteMarkerRank

end

end OAI

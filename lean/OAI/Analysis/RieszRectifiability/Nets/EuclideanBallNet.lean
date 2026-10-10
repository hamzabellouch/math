import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.EuclideanPackingBound

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_euclidean_ball_net {k : ℕ} (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ s : Finset (Ambient k),
      (∀ x ∈ s, ‖x‖ ≤ R) ∧
      (∀ x : Ambient k, ‖x‖ ≤ R → ∃ y ∈ s, dist x y < δ) ∧
      (s.card : ℝ) * (δ / 2) ^ k ≤ (R + δ / 2) ^ k := by
  classical
  let P : Finset (Ambient k) → Prop := fun s =>
    (∀ x ∈ s, ‖x‖ ≤ R) ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y
  have hr : 0 < δ / 2 := by positivity
  have hcount : ∀ s, P s → (s.card : ℝ) ≤ ((R + δ / 2) / (δ / 2)) ^ k := by
    intro s hs
    apply euclidean_separated_card_le s R (δ / 2) hR hr hs.1
    intro x hx y hy hxy
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using! hs.2 x hx y hy hxy
  let cards : Set ℕ := {m | ∃ s : Finset (Ambient k), P s ∧ s.card = m}
  have hne : cards.Nonempty := ⟨0, ∅, by simp [P], rfl⟩
  obtain ⟨B, hB⟩ := exists_nat_gt (((R + δ / 2) / (δ / 2)) ^ k)
  have hbdd : BddAbove cards := by
    refine ⟨B, ?_⟩
    rintro m ⟨s, hs, rfl⟩
    exact_mod_cast (hcount s hs).trans hB.le
  obtain ⟨s, hs, hcard⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ t, P t → t.card ≤ s.card := by
    intro t ht
    rw [hcard]
    exact le_csSup hbdd ⟨t, ht, rfl⟩
  refine ⟨s, hs.1, ?_, ?_⟩
  · intro x hx
    by_contra hmissing
    have hfar : ∀ y ∈ s, δ ≤ dist x y := by
      intro y hy
      exact le_of_not_gt (fun h => hmissing ⟨y, hy, h⟩)
    have hnot : x ∉ s := by
      intro hxmem
      have h := hfar x hxmem
      rw [dist_self] at h
      exact (not_le_of_gt hδ) h
    have hnew : P (insert x s) := by
      constructor
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact hs.1 y hy
      · intro u hu v hv huv
        rcases Finset.mem_insert.mp hu with rfl | hsu
        · rcases Finset.mem_insert.mp hv with rfl | hsv
          · exact (huv rfl).elim
          · exact hfar v hsv
        · rcases Finset.mem_insert.mp hv with rfl | hsv
          · simpa only [dist_comm] using! hfar u hsu
          · exact hs.2 u hsu v hsv huv
    have h := hmax (insert x s) hnew
    rw [Finset.card_insert_of_notMem hnot] at h
    omega
  · apply euclidean_separated_card_mul_radius_pow_le s R (δ / 2) hR hr hs.1
    intro x hx y hy hxy
    have h := hs.2 x hx y hy hxy
    linarith

end

end RieszRectifiability

end OAI

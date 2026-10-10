import Mathlib
import OAI.Combinatorics.UniformKServer.BoundedFilter

namespace OAI

namespace UniformKServer.RawBlockCharge

theorem paid_or_covered {n k : ℕ} (d : RationalMetric n) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (h : History n k) (s : Configuration n k) :
    δ ≤ costAlong d s h ∨ (∀ r ∈ h.map Prod.fst, ∃ j, s j = r) := by
  induction h generalizing s with
  | nil => exact Or.inr (by simp)
  | cons a h ih =>
    rcases a with ⟨r,j⟩
    by_cases hj : s j = r
    · have he : serve s r j = s := by
        unfold serve
        conv_lhs => arg 3; rw [← hj]
        exact Function.update_eq_self _ _
      have hz : (d.distance (s j) r : ℝ) = 0 := by
        rw [hj, (d.eq_zero r r).mpr rfl, Rat.cast_zero]
      rcases ih s with hp | hc
      · exact Or.inl (by simpa only [costAlong, hz, he, zero_add] using hp)
      · right
        intro x hx
        simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨j,hj⟩
        · exact hc x hx
    · left
      exact (hsep _ _ hj).trans (le_add_of_nonneg_right (costAlong_nonneg d _ _))

theorem one_block {n k : ℕ} (d : RationalMetric n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (s : Configuration n k) (h : History n k)
    (hc : k < (h.map Prod.fst).toFinset.card) : δ ≤ costAlong d s h := by
  classical
  rcases paid_or_covered d δ hδ hsep h s with hp | hs
  · exact hp
  · have hsub : (h.map Prod.fst).toFinset ⊆ Finset.univ.image s := by
      intro r hr
      obtain ⟨j,hj⟩ := hs r (List.mem_toFinset.mp hr)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    have hn : (h.map Prod.fst).toFinset.card ≤ k := calc
      _ ≤ (Finset.univ.image s).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
    omega

theorem cost_append {n k : ℕ} (d : RationalMetric n) (g h : History n k)
    (s : Configuration n k) :
    costAlong d s (g++h) = costAlong d s g + costAlong d (finish s g) h := by
  induction g generalizing s with
  | nil => simp [costAlong, finish]
  | cons a g ih => cases a; simp [costAlong, finish, ih, add_assoc]

theorem split_history {n k : ℕ} (h : History n k) (w v : List (Fin n))
    (hw : h.map Prod.fst = w++v) :
    ∃ g t, h = g++t ∧ g.map Prod.fst = w ∧ t.map Prod.fst = v := by
  refine ⟨h.take w.length, h.drop w.length, (List.take_append_drop _ _).symm, ?_, ?_⟩
  · rw [List.map_take, hw, List.take_left]
  · rw [List.map_drop, hw, List.drop_left]

theorem tail_blocks {n k : ℕ} (d : RationalMetric n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (blocks : List (List (Fin n))) (hb : ∀ b ∈ blocks, k < b.toFinset.card)
    (tail : List (Fin n)) (s : Configuration n k) (h : History n k)
    (hw : h.map Prod.fst = blocks.flatten ++ tail) :
    (blocks.length : ℝ)*δ ≤ costAlong d s h := by
  induction blocks generalizing s h with
  | nil => simpa only [List.length_nil, Nat.cast_zero, zero_mul] using costAlong_nonneg d s h
  | cons b blocks ih =>
    obtain ⟨g,t,rfl,hg,ht⟩ := split_history h b (blocks.flatten++tail)
      (by simpa only [List.flatten_cons, List.append_assoc] using hw)
    have hgcost := one_block d δ hδ hsep s g (by rw [hg]; exact hb b (by simp))
    have htCost := ih (fun b' hb' => hb b' (by simp [hb'])) (finish s g) t ht
    rw [cost_append]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem word_blocks {n k : ℕ} (d : RationalMetric n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (blocks : List (List (Fin n))) (hb : ∀ b ∈ blocks, k < b.toFinset.card)
    (pre tail : List (Fin n)) (s : Configuration n k) (h : History n k)
    (hw : h.map Prod.fst = pre ++ blocks.flatten ++ tail) :
    (blocks.length : ℝ)*δ ≤ costAlong d s h := by
  obtain ⟨g,t,rfl,hg,ht⟩ := split_history h pre (blocks.flatten++tail)
    (by simpa only [List.append_assoc] using hw)
  have hp := tail_blocks d δ hδ hsep blocks hb tail (finish s g) t ht
  rw [cost_append]
  linarith [costAlong_nonneg d s g]

theorem offline_blocks {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (blocks : List (List (Fin n))) (hb : ∀ b ∈ blocks, k < b.toFinset.card)
    (pre tail : List (Fin n)) (s : Configuration n k) :
    (blocks.length : ℝ)*δ ≤ offlineCost d s (pre ++ blocks.flatten ++ tail) := by
  apply le_csInf
  · let h : History n k := (pre++blocks.flatten++tail).map (fun r => (r,⟨0,hk⟩))
    refine ⟨costAlong d s h, h, ?_, rfl⟩
    change ((pre++blocks.flatten++tail).map (fun r => (r, (⟨0,hk⟩ : Fin k)))).map Prod.fst = _
    rw [List.map_map]
    exact List.map_id _
  · rintro c ⟨h,hw,rfl⟩
    exact word_blocks d δ hδ hsep blocks hb pre tail s h hw

end UniformKServer.RawBlockCharge


end OAI

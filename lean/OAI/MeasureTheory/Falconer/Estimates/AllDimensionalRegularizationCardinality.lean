import OAI.MeasureTheory.Falconer.Estimates.AllDimensionalRegularizationLabels

namespace OAI

/-!
# Dimension-dependent counts for regularization labels

A selected-depth gap of length b-a has at most 2^(d*(b-a))
children, so its logarithmic count bin has d*(b-a)+1 possibilities.
The number of final labels is polynomial in terminal depth when the
number of selected blocks is fixed.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem labeledChildren_subset_extensions {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) :
    labeledChildren L f a b p ⊆ (cubePaths d (b-a)).image (fun q => p.take a ++ q) := by
  classical
  intro c hc
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hq,ha,_⟩ := Finset.mem_filter.mp hq
  have hlen : q.length = N := (mem_cubePaths d N q).mp (hL hq)
  refine Finset.mem_image.mpr ⟨(q.take b).drop a, ?_, ?_⟩
  · simp only [mem_cubePaths, List.length_drop, List.length_take, hlen,
      Nat.min_eq_left hbN]
  · have he := List.take_append_drop a (q.take b)
    simpa only [List.take_take, Nat.min_eq_left hab, ha] using he

theorem labeledChildren_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : (labeledChildren L f a b p).card ≤ 2 ^ (d*(b-a)) :=
  (Finset.card_le_card (labeledChildren_subset_extensions hab hbN hL f p)).trans
    (Finset.card_image_le.trans_eq (card_cubePaths d (b-a)))

theorem child_bin_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : Nat.log 2 (labeledChildren L f a b p).card ≤ d*(b-a) := by
  have hc := labeledChildren_card_le hab hbN hL f p
  have := Nat.log_mono_right (b := 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2)] using this

theorem extendLabel_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ) :
    (L.image (extendLabel L a b f)).card ≤ (d*(b-a)+1) * (L.image f).card := by
  classical
  let S := (Finset.range (d*(b-a)+1)).product (L.image f)
  have hs : L.image (extendLabel L a b f) ⊆ S.image (fun z => z.1 :: z.2) := by
    intro T hT
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨(Nat.log 2 (labeledChildren L f a b p).card, f p),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (child_bin_le hab hbN hL f p)),
        Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩,rfl⟩
  calc
    _ ≤ (S.image (fun z => z.1 :: z.2)).card := Finset.card_le_card hs
    _ ≤ S.card := Finset.card_image_le
    _ = _ := by simp [S]

theorem upwardLabels_card_le {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (steps : List (ℕ × ℕ)) (hsteps : ∀ s ∈ steps, s.1 ≤ s.2 ∧ s.2 ≤ N)
    (f : CellPath d → List ℕ) :
    (L.image (upwardLabels L steps f)).card ≤ (d*N+1)^steps.length * (L.image f).card := by
  classical
  induction steps generalizing f with
  | nil => simp [upwardLabels]
  | cons s steps ih =>
    have hs := hsteps s (List.mem_cons_self)
    have htail := ih (fun entry hentry => hsteps entry (List.mem_cons_of_mem _ hentry))
      (extendLabel L s.1 s.2 f)
    have hone := extendLabel_card_le hs.1 hs.2 hL f
    have hbound : d*(s.2-s.1)+1 ≤ d*N+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left d ((Nat.sub_le s.2 s.1).trans hs.2)) 1
    calc
      _ ≤ (d*N+1)^steps.length * (L.image (extendLabel L s.1 s.2 f)).card := htail
      _ ≤ (d*N+1)^steps.length * ((d*N+1)*(L.image f).card) :=
        Nat.mul_le_mul_left _ (hone.trans (Nat.mul_le_mul_right _ hbound))
      _ = _ := by simp only [List.length_cons, pow_succ, Nat.mul_assoc]

end Falconer.Regularization

end OAI

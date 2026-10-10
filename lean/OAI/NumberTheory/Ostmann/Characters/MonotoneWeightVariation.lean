import OAI.NumberTheory.Ostmann.Characters.WeightedPhaseExtraction

namespace OAI

/-! # Variation of the smooth factors on monotone argument intervals -/

namespace Ostmann

open scoped BigOperators

theorem discreteVariation_comp_monotone (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hrange : ∀ j ≤ N - 1, lo ≤ u j ∧ u j ≤ hi)
    (hmono : ∀ j < N - 1, u j ≤ u (j + 1)) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hs : (∑ j ∈ Finset.range (N - 1), ‖Φ (u (j + 1)) - Φ (u j)‖) ≤
      D * (u (N - 1) - u 0) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N - 1), D * (u (j + 1) - u j) := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [abs_of_nonneg (sub_nonneg.mpr (hmono j (Finset.mem_range.mp hj)))] using
          hlip (u (j + 1)) (u j)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]
  have hwidth : u (N - 1) - u 0 ≤ hi - lo := by
    have h1 := (hrange (N - 1) le_rfl).2
    have h0 := (hrange 0 (Nat.zero_le _)).1
    linarith
  unfold discreteVariation
  exact add_le_add (hbound _) (hs.trans (mul_le_mul_of_nonneg_left hwidth hD))

def clipRealInterval (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem clipRealInterval_bounds (lo hi x : ℝ) (h : lo ≤ hi) :
    lo ≤ clipRealInterval lo hi x ∧ clipRealInterval lo hi x ≤ hi := by
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem clipRealInterval_monotone (lo hi : ℝ) : Monotone (clipRealInterval lo hi) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

/-- Compact support allows clipping an unbounded monotone argument before
applying the Lipschitz estimate. The cost depends on the support width. -/
theorem compact_weight_clip (Φ : ℝ → ℂ) (lo hi : ℝ) (h : lo ≤ hi)
    (hlo : Φ lo = 0) (hhi : Φ hi = 0)
    (hout : ∀ x, x < lo ∨ hi < x → Φ x = 0) (x : ℝ) :
    Φ (clipRealInterval lo hi x) = Φ x := by
  by_cases hx : x < lo
  · have hclip : clipRealInterval lo hi x = lo := by
      unfold clipRealInterval
      exact max_eq_left ((min_le_right _ _).trans hx.le)
    rw [hclip, hlo, hout x (Or.inl hx)]
  · by_cases hy : hi < x
    · have hclip : clipRealInterval lo hi x = hi := by
        simp only [clipRealInterval, min_eq_left hy.le, max_eq_right h]
      rw [hclip, hhi, hout x (Or.inr hy)]
    · simp only [clipRealInterval, min_eq_right (le_of_not_gt hy),
        max_eq_right (le_of_not_gt hx)]

theorem discreteVariation_comp_compact_monotone (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hlohi : lo ≤ hi) (hD : 0 ≤ D)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hlo : Φ lo = 0) (hhi : Φ hi = 0)
    (hout : ∀ x, x < lo ∨ hi < x → Φ x = 0)
    (hmono : ∀ j < N - 1, u j ≤ u (j + 1)) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have he : (fun j => Φ (clipRealInterval lo hi (u j))) = fun j => Φ (u j) := by
    funext j
    exact compact_weight_clip Φ lo hi hlohi hlo hhi hout (u j)
  rw [← he]
  apply discreteVariation_comp_monotone Φ _ lo hi B D N hD hbound hlip
  · intro j _
    exact clipRealInterval_bounds lo hi (u j) hlohi
  · intro j hj
    exact clipRealInterval_monotone lo hi (hmono j hj)

theorem discreteVariation_comp_compact_antitone (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hlohi : lo ≤ hi) (hD : 0 ≤ D)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hlo : Φ lo = 0) (hhi : Φ hi = 0)
    (hout : ∀ x, x < lo ∨ hi < x → Φ x = 0)
    (hanti : ∀ j < N - 1, u (j + 1) ≤ u j) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hb := discreteVariation_comp_compact_monotone (fun x => Φ (-x)) (fun j => -u j)
    (-hi) (-lo) B D N (neg_le_neg hlohi) hD (fun x => hbound (-x))
    (fun x y => by simpa only [neg_sub_neg, abs_sub_comm] using hlip (-x) (-y))
    (by simpa using hhi) (by simpa using hlo)
    (fun x hx => hout (-x) (by
      rcases hx with hx | hx
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)))
    (fun j hj => neg_le_neg (hanti j hj))
  simpa only [neg_neg, neg_sub_neg] using hb

/-- Only bounds on the actual compact argument interval are needed. -/
theorem discreteVariation_comp_monotoneOn (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Set.Icc lo hi, ‖Φ x‖ ≤ B)
    (hlip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hrange : ∀ j ≤ N - 1, u j ∈ Set.Icc lo hi)
    (hmono : ∀ j < N - 1, u j ≤ u (j + 1)) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hs : (∑ j ∈ Finset.range (N - 1), ‖Φ (u (j + 1)) - Φ (u j)‖) ≤
      D * (u (N - 1) - u 0) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N - 1), D * (u (j + 1) - u j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        simpa only [abs_of_nonneg (sub_nonneg.mpr (hmono j hj'))] using
          hlip (u (j + 1)) (hrange (j + 1) (by omega)) (u j) (hrange j (by omega))
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]
  have hw : u (N - 1) - u 0 ≤ hi - lo := by
    have h1 := (hrange (N - 1) le_rfl).2
    have h0 := (hrange 0 (Nat.zero_le _)).1
    linarith
  exact add_le_add (hbound _ (hrange _ le_rfl))
    (hs.trans (mul_le_mul_of_nonneg_left hw hD))

theorem discreteVariation_comp_antitoneOn (Φ : ℝ → ℂ) (u : ℕ → ℝ)
    (lo hi B D : ℝ) (N : ℕ) (hD : 0 ≤ D)
    (hbound : ∀ x ∈ Set.Icc lo hi, ‖Φ x‖ ≤ B)
    (hlip : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
      ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hrange : ∀ j ≤ N - 1, u j ∈ Set.Icc lo hi)
    (hanti : ∀ j < N - 1, u (j + 1) ≤ u j) :
    discreteVariation (fun j => Φ (u j)) N ≤ B + D * (hi - lo) := by
  have hs : (∑ j ∈ Finset.range (N - 1), ‖Φ (u (j + 1)) - Φ (u j)‖) ≤
      D * (u 0 - u (N - 1)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N - 1), D * (u j - u (j + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hh := hlip (u (j + 1)) (hrange (j + 1) (by omega)) (u j) (hrange j (by omega))
        rw [abs_of_nonpos (sub_nonpos.mpr (hanti j hj'))] at hh
        convert hh using 1
        ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub']
  have hw : u 0 - u (N - 1) ≤ hi - lo := by
    have h1 := (hrange (N - 1) le_rfl).1
    have h0 := (hrange 0 (Nat.zero_le _)).2
    linarith
  exact add_le_add (hbound _ (hrange _ le_rfl))
    (hs.trans (mul_le_mul_of_nonneg_left hw hD))

end Ostmann

end OAI

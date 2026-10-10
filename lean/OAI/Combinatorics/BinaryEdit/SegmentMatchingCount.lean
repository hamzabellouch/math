import OAI.Combinatorics.BinaryEdit.RandomMatching

namespace OAI

namespace TreeEdit.BinaryLower.RandomMatching

/-- A choice of positions for a subsequence, in their original order. -/
abbrev IncreasingPositions (a s : ℕ) := {f : Fin s → Fin a // StrictMono f}

noncomputable def increasingPositionsEquiv (a s : ℕ) :
    IncreasingPositions a s ≃ {t : Finset (Fin a) // t.card = s} := by
  classical
  refine
    { toFun := fun f => ⟨Finset.univ.image f.1, by
        rw [Finset.card_image_of_injective _ f.2.injective]
        simp⟩
      invFun := fun t => ⟨t.1.orderEmbOfFin t.2, (t.1.orderEmbOfFin t.2).strictMono⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique (by
      rw [Finset.card_image_of_injective _ f.2.injective]
      simp) (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩) f.2).symm
  · intro t
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ t.1 t.2

theorem card_increasingPositions (a s : ℕ) :
    Nat.card (IncreasingPositions a s) = a.choose s := by
  classical
  rw [Nat.card_congr (increasingPositionsEquiv a s), Nat.card_eq_fintype_card]
  simp

/-- The event that two fixed windows admit a matching of size `s`. -/
noncomputable def segmentMatchingEvent {K P a : ℕ} (s : ℕ)
    (i j : Fin K) (u v : Fin a → Fin P) :
    Finset (Fin K → Fin P → Bool) := by
  classical
  exact Finset.univ.filter fun c =>
    ∃ f g : IncreasingPositions a s, ∀ t, c i (u (f.1 t)) = c j (v (g.1 t))

/-- Finite union estimate for one pair of unequal-label windows. -/
theorem card_segmentMatchingEvent_le {K P a s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin a → Fin P)
    (hv : Function.Injective v) :
    (segmentMatchingEvent s i j u v).card ≤
      (a.choose s) ^ 2 * 2 ^ (K * P - s) := by
  classical
  let event (fg : IncreasingPositions a s × IncreasingPositions a s) :=
    Finset.univ.filter fun c : Fin K → Fin P → Bool =>
      ∀ t, c i (u (fg.1.1 t)) = c j (v (fg.2.1 t))
  have hcard (fg : IncreasingPositions a s × IncreasingPositions a s) :
      (event fg).card = 2 ^ (K * P - s) :=
    filter_card_prescribed_matching i j hne (u ∘ fg.1.1) (v ∘ fg.2.1)
      (hv.comp fg.2.2.injective)
  have heq : segmentMatchingEvent s i j u v = Finset.univ.biUnion event := by
    ext c
    simp only [segmentMatchingEvent, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_biUnion, event]
    constructor
    · rintro ⟨f, g, hfg⟩
      exact ⟨(f, g), hfg⟩
    · rintro ⟨⟨f, g⟩, hfg⟩
      exact ⟨f, g, hfg⟩
  have hc : Fintype.card (IncreasingPositions a s) = a.choose s := by
    simpa only [Nat.card_eq_fintype_card] using card_increasingPositions a s
  rw [heq]
  calc
    (Finset.univ.biUnion event).card ≤ ∑ fg, (event fg).card := Finset.card_biUnion_le
    _ = (a.choose s) ^ 2 * 2 ^ (K * P - s) := by
      simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_prod, hc,
        smul_eq_mul, pow_two]

/-- The fixed-window union bound in normalized counting-measure form. -/
theorem segmentMatchingEvent_fraction_le {K P a s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin a → Fin P)
    (hv : Function.Injective v) (hs : s ≤ a) :
    ((segmentMatchingEvent s i j u v).card : ℝ) / (2 : ℝ) ^ (K * P) ≤
      ((a.choose s : ℝ) ^ 2) / (2 : ℝ) ^ s := by
  have ha : a ≤ P := by simpa using Fintype.card_le_of_injective v hv
  have hK : 1 ≤ K := by have := i.isLt; omega
  have hsKP : s ≤ K * P := by nlinarith
  have hmul : (segmentMatchingEvent s i j u v).card * 2 ^ s ≤
      (a.choose s) ^ 2 * 2 ^ (K * P) := by
    calc
      _ ≤ ((a.choose s) ^ 2 * 2 ^ (K * P - s)) * 2 ^ s :=
        Nat.mul_le_mul_right _ (card_segmentMatchingEvent_le i j hne u v hv)
      _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hsKP]
  apply (div_le_div_iff₀ (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)).2
  exact_mod_cast hmul

end TreeEdit.BinaryLower.RandomMatching

end OAI

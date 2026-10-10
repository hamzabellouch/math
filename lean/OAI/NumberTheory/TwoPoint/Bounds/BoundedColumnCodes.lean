import OAI.NumberTheory.TwoPoint.Walks.ColumnDecoderAsymptotics

namespace OAI

/-! One code universe when segment, omitted-run and imperfect counts vary. -/

namespace TwoPointCorrelations

open Finset Filter

abbrev BoundedColumnDecoderCode (N segments omitted imperfect : ℕ) :=
  Σ s : Fin (segments + 1), Σ o : Fin (omitted + 1), Σ i : Fin (imperfect + 1),
    ColumnDecoderCode N s.val o.val i.val

/-- Taking the union over the permitted counts costs only three polynomial
factors. It does not impose common counts on different realizations. -/
theorem card_boundedColumnDecoderCode_le (N segments omitted imperfect : ℕ) (hN : 1 ≤ N) :
    Fintype.card (BoundedColumnDecoderCode N segments omitted imperfect) ≤
      ((segments + 1) * (omitted + 1) * (imperfect + 1)) *
        (2 ^ (6 * N + 1) * N ^ (2 * segments + omitted + imperfect)) := by
  simp only [BoundedColumnDecoderCode, Fintype.card_sigma]
  calc
    _ ≤ ∑ _s : Fin (segments + 1), ∑ _o : Fin (omitted + 1), ∑ _i : Fin (imperfect + 1),
        (2 ^ (6 * N + 1) * N ^ (2 * segments + omitted + imperfect)) := by
      apply sum_le_sum
      intro s _
      apply sum_le_sum
      intro o _
      apply sum_le_sum
      intro i _
      apply (card_columnDecoderCode_le N s.val o.val i.val).trans
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right hN (by omega)
    _ = _ := by simp [mul_assoc]

noncomputable def decodeBoundedColumnPattern {N segments omitted imperfect : ℕ}
    (code : BoundedColumnDecoderCode N segments omitted imperfect) : Fin N → Fin N → Bool :=
  decodeColumnPattern code.2.2.2

/-- This is the full coefficient-independent image, including all permitted
segment and exceptional-position counts. -/
theorem card_bounded_column_patterns (N segments omitted imperfect : ℕ) (hN : 1 ≤ N) :
    Nat.card (Set.range (@decodeBoundedColumnPattern N segments omitted imperfect)) ≤
      ((segments + 1) * (omitted + 1) * (imperfect + 1)) *
        (2 ^ (6 * N + 1) * N ^ (2 * segments + omitted + imperfect)) := by
  let f := @decodeBoundedColumnPattern N segments omitted imperfect
  have hr : Nat.card (Set.range f) ≤ Nat.card (BoundedColumnDecoderCode N segments omitted imperfect) :=
    Nat.card_le_card_of_surjective (fun c => (⟨f c, c, rfl⟩ : Set.range f)) (by
      rintro ⟨_, c, rfl⟩
      exact ⟨c, rfl⟩)
  exact hr.trans (by simpa only [Nat.card_eq_fintype_card] using
    card_boundedColumnDecoderCode_le N segments omitted imperfect hN)

/-- The union over all bounded counts still has an absolute exponential
cost. Fixed constants in the sublinear budget affect only the threshold. -/
theorem eventually_bounded_column_code_exponential (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ k N segments omitted imperfect : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ N → N ≤ 4 * k →
      segments ≤ N → omitted ≤ N → imperfect ≤ N →
      ((2 * segments + omitted + imperfect : ℕ) : ℝ) ≤ C * L ^ (0.92 : ℝ) →
      (Fintype.card (BoundedColumnDecoderCode N segments omitted imperfect) : ℝ) ≤
        Real.exp (64 * k) := by
  filter_upwards [eventually_column_decoder_exponential C hC] with L hcode
  intro k N segments omitted imperfect hklo hkhi hN hNk hS hO hI hbudget
  have heach (s : Fin (segments + 1)) (o : Fin (omitted + 1)) (i : Fin (imperfect + 1)) :
      (Fintype.card (ColumnDecoderCode N s.val o.val i.val) : ℝ) ≤ Real.exp (52 * k) := by
    apply hcode k N s.val o.val i.val hklo hkhi hN hNk
    apply le_trans _ hbudget
    exact_mod_cast (show 2 * s.val + o.val + i.val ≤ 2 * segments + omitted + imperfect by omega)
  have hfactor (a : ℕ) (ha : a ≤ N) : (a : ℝ) + 1 ≤ Real.exp N := by
    have h : (a : ℝ) ≤ N := by exact_mod_cast ha
    linarith [Real.add_one_le_exp (N : ℝ)]
  have hcounts : ((segments : ℝ) + 1) * (omitted + 1) * (imperfect + 1) ≤
      Real.exp (3 * N) := by
    calc
      _ ≤ Real.exp N * Real.exp N * Real.exp N := by
        gcongr
        · exact hfactor segments hS
        · exact hfactor omitted hO
        · exact hfactor imperfect hI
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc
    _ = ∑ s : Fin (segments + 1), ∑ o : Fin (omitted + 1), ∑ i : Fin (imperfect + 1),
        (Fintype.card (ColumnDecoderCode N s.val o.val i.val) : ℝ) := by
      simp only [BoundedColumnDecoderCode, Fintype.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _s : Fin (segments + 1), ∑ _o : Fin (omitted + 1), ∑ _i : Fin (imperfect + 1),
        Real.exp (52 * k) := by
      exact sum_le_sum (fun s _ => sum_le_sum (fun o _ => sum_le_sum (fun i _ => heach s o i)))
    _ = (((segments : ℝ) + 1) * (omitted + 1) * (imperfect + 1)) * Real.exp (52 * k) := by
      simp [mul_assoc]
    _ ≤ Real.exp (3 * N) * Real.exp (52 * k) :=
      mul_le_mul_of_nonneg_right hcounts (Real.exp_pos _).le
    _ = Real.exp (3 * N + 52 * k) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (64 * k) := by
      apply Real.exp_le_exp.mpr
      have h : (N : ℝ) ≤ 4 * k := by exact_mod_cast hNk
      linarith

end TwoPointCorrelations

end OAI

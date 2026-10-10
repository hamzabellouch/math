import OAI.Probability.SwitchChain.VariableBlockVariance

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.BalancedBlockVariance
open FixedBlockMarginal (average)
open VariableBlockVariance (Family sizes rowFunction)

variable (U W : Type*) [Fintype U] [sectionDecidableEqU : DecidableEq U] [Fintype W] [sectionDecidableEqW : DecidableEq W]

abbrev Balanced (u w : Fin 3 → ℕ) :=
  {c : (U → Fin 3) × (W → Fin 3) // ∀ i,
    (FixedBlock.row c.1 i).card + w i = (FixedBlock.row c.2 i).card + u i}

variable {U W}

theorem sum_row_card {A : Type*} [Fintype A] [DecidableEq A] (c : A → Fin 3) :
    (∑ i, (FixedBlock.row c i).card) = Fintype.card A := by
  simp only [FixedBlock.row, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

include sectionDecidableEqU sectionDecidableEqW in
theorem lower_le {u w : Fin 3 → ℕ} (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (c : Balanced U W u w) (i : Fin 3) : w i ≤ (FixedBlock.row c.val.2 i).card := by
  have retainedsectionDecidableEqU := sectionDecidableEqU
  have retainedsectionDecidableEqW := sectionDecidableEqW
  have h := c.property i
  rcases hsep i with h | h <;> omega

theorem lower_sum_le {u w : Fin 3 → ℕ} (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (c : Balanced U W u w) : (∑ i, w i) ≤ Fintype.card W := by
  rw [← sum_row_card c.val.2]
  exact Finset.sum_le_sum (fun i _ => lower_le hsep c i)

theorem totals {u w : Fin 3 → ℕ} (c : Balanced U W u w) :
    Fintype.card U + ∑ i, w i = Fintype.card W + ∑ i, u i := by
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => c.property i)
  simpa only [Finset.sum_add_distrib, sum_row_card] using h

def countVector {u w : Fin 3 → ℕ} (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (c : Balanced U W u w) : TripleCountLaw.Triple (Fintype.card W - ∑ i, w i) := by
  let m := Fintype.card W - ∑ i, w i
  have hs : (∑ i, ((FixedBlock.row c.val.2 i).card - w i)) = m := by
    rw [Finset.sum_tsub_distrib]
    · simp only [sum_row_card, m]
    · intro i hi
      exact lower_le hsep c i
  refine ⟨fun i => ⟨(FixedBlock.row c.val.2 i).card - w i, ?_⟩, hs⟩
  have hi : (FixedBlock.row c.val.2 i).card - w i ≤
      ∑ j, ((FixedBlock.row c.val.2 j).card - w j) :=
    Finset.single_le_sum (f := fun j => (FixedBlock.row c.val.2 j).card - w j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hs] at hi
  omega

def forgetCounts (u w : Fin 3 → ℕ)
    (z : Family U W (Fintype.card W - ∑ i, w i) u w) : Balanced U W u w :=
  ⟨(z.2.1.val, z.2.2.val), by
    intro i
    rw [z.2.1.property i, z.2.2.property i]
    simp only [sizes]
    omega⟩

def familyEquiv (u w : Fin 3 → ℕ) (hsep : ∀ i, u i = 0 ∨ w i = 0) :
    Balanced U W u w ≃ Family U W (Fintype.card W - ∑ i, w i) u w := by
  apply Equiv.symm
  apply Equiv.ofBijective (forgetCounts (U := U) (W := W) u w)
  constructor
  · rintro ⟨x, c, d⟩ ⟨y, e, f⟩ h
    have hc : c.val = e.val := congrArg (fun z : Balanced U W u w => z.val.1) h
    have hd : d.val = f.val := congrArg (fun z : Balanced U W u w => z.val.2) h
    have hxy : x = y := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      have hi := congrArg (fun v : W → Fin 3 => (FixedBlock.row v i).card) hd
      rw [d.property i, f.property i] at hi
      simp only [sizes] at hi
      omega
    subst y
    have hce : c = e := Subtype.ext hc
    have hdf : d = f := Subtype.ext hd
    subst e
    subst f
    rfl
  · intro c
    refine ⟨⟨countVector hsep c, ⟨⟨c.val.1, ?_⟩, ⟨c.val.2, ?_⟩⟩⟩, rfl⟩
    · intro i
      have he := c.property i
      have hl := lower_le hsep c i
      change (FixedBlock.row c.val.1 i).card =
        (FixedBlock.row c.val.2 i).card - w i + u i
      omega
    · intro i
      change (FixedBlock.row c.val.2 i).card =
        (FixedBlock.row c.val.2 i).card - w i + w i
      exact (Nat.sub_add_cancel (lower_le hsep c i)).symm

theorem row_variance_bound (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    [Nonempty (Balanced U W u w)]
    (g : Fin 3 → Finset U → Finset W → ℝ) :
    FiniteVariance.variance (fun c : Balanced U W u w =>
      ∑ i, g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i)) ≤
      2 * ∑ i, FiniteVariance.variance (fun c : Balanced U W u w =>
        g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i)) := by
  obtain ⟨c⟩ := ‹Nonempty (Balanced U W u w)›
  have hw := lower_sum_le hsep c
  have ht := totals c
  let m := Fintype.card W - ∑ i, w i
  have hW : m + ∑ i, w i = Fintype.card W := Nat.sub_add_cancel hw
  have hU : m + ∑ i, u i = Fintype.card U := by omega
  let e := familyEquiv (U := U) (W := W) u w hsep
  have h := VariableBlockVariance.row_variance_bound m u w hsep hU hW g
  have he (f : Balanced U W u w → ℝ) :
      FiniteVariance.variance (fun z => f (e.symm z)) = FiniteVariance.variance f :=
    FiniteVariance.variance_equiv e.symm f
  rw [← he (fun c => ∑ i, g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i))]
  simp_rw [← he (fun c => g _ (FixedBlock.row c.val.1 _) (FixedBlock.row c.val.2 _))]
  exact h

theorem row_variance_bound_of_rowInvariant (u w : Fin 3 → ℕ)
    (hsep : ∀ i, u i = 0 ∨ w i = 0)
    [Nonempty (Balanced U W u w)]
    (f : Fin 3 → Balanced U W u w → ℝ)
    (hf : ∀ i c d,
      FixedBlock.row c.val.1 i = FixedBlock.row d.val.1 i →
      FixedBlock.row c.val.2 i = FixedBlock.row d.val.2 i → f i c = f i d) :
    FiniteVariance.variance (fun c => ∑ i, f i c) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  classical
  let g (i : Fin 3) (s : Finset U) (t : Finset W) : ℝ :=
    if h : ∃ c : Balanced U W u w,
        FixedBlock.row c.val.1 i = s ∧ FixedBlock.row c.val.2 i = t then
      f i (Classical.choose h) else 0
  have hg (i : Fin 3) (c : Balanced U W u w) :
      g i (FixedBlock.row c.val.1 i) (FixedBlock.row c.val.2 i) = f i c := by
    have hex : ∃ d : Balanced U W u w,
        FixedBlock.row d.val.1 i = FixedBlock.row c.val.1 i ∧
        FixedBlock.row d.val.2 i = FixedBlock.row c.val.2 i := ⟨c, rfl, rfl⟩
    dsimp only [g]
    rw [dite_eq_left hex]
    exact hf i _ c (Classical.choose_spec hex).1 (Classical.choose_spec hex).2
  have h := row_variance_bound u w hsep g
  simpa only [hg] using h

end Problem315.BalancedBlockVariance

end

end OAI

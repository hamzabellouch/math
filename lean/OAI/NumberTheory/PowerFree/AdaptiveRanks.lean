import OAI.NumberTheory.PowerFree.PatchBounds

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators

namespace QuarticPowerFree

noncomputable def equationRank {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : Submodule K V) : ℕ := Module.finrank K (V ⧸ W)

theorem equationRank_mono {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {W W' : Submodule K V} (h : W ≤ W') :
    equationRank W' ≤ equationRank W := by
  simp only [equationRank, Submodule.finrank_quotient]
  exact Nat.sub_le_sub_left (Submodule.finrank_mono h) _

theorem equationRank_eq_iff_of_le {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {W W' : Submodule K V} (h : W ≤ W') :
    equationRank W = equationRank W' ↔ W = W' := by
  constructor
  · intro he
    apply Submodule.eq_of_le_of_finrank_eq h
    have h₁ := Submodule.finrank_quotient_add_finrank W
    have h₂ := Submodule.finrank_quotient_add_finrank W'
    dsimp [equationRank] at he
    omega
  · rintro rfl; rfl

variable {K V σ α : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (W : ℕ → σ → α → Submodule K V)
variable (next : ℕ → σ → Submodule K V → σ)

noncomputable def adaptiveCode : ℕ → ℕ → σ → α → ℕ
  | 0, _, _, _ => 0
  | n+1, i, s, a => equationRank (W i s a) * (Module.finrank K V + 1)^n +
      adaptiveCode n (i+1) (next i s (W i s a)) a

noncomputable def adaptiveStates : ℕ → ℕ → σ → α → List σ
  | 0, _, s, _ => [s]
  | n+1, i, s, a => s :: adaptiveStates n (i+1) (next i s (W i s a)) a

variable [Module.Finite K V]

theorem adaptiveCode_lt (n i : ℕ) (s : σ) (a : α) :
    adaptiveCode W next n i s a < (Module.finrank K V + 1)^n := by
  induction n generalizing i s with
  | zero => simp [adaptiveCode]
  | succ n ih =>
    have hr : equationRank (W i s a) ≤ Module.finrank K V := by
      rw [equationRank, Submodule.finrank_quotient]
      exact Nat.sub_le _ _
    have ht := ih (i+1) (next i s (W i s a))
    simp only [adaptiveCode, pow_succ]
    nlinarith

theorem adaptiveCode_mono_stable (a b : α)
    (hW : ∀ i s, W i s a ≤ W i s b) (n i : ℕ) (s : σ) :
    adaptiveCode W next n i s b ≤ adaptiveCode W next n i s a ∧
    (adaptiveCode W next n i s b = adaptiveCode W next n i s a →
      adaptiveStates W next n i s b = adaptiveStates W next n i s a) := by
  induction n generalizing i s with
  | zero => simp [adaptiveCode, adaptiveStates]
  | succ n ih =>
    have hr := equationRank_mono (hW i s)
    by_cases he : equationRank (W i s a) = equationRank (W i s b)
    · have hw := (equationRank_eq_iff_of_le (hW i s)).mp he
      have hh := ih (i+1) (next i s (W i s a))
      simp only [adaptiveCode, adaptiveStates, ← hw]
      exact ⟨Nat.add_le_add_left hh.1 _, fun h => congrArg (List.cons s) (hh.2 (Nat.add_left_cancel h))⟩
    · have hl : equationRank (W i s b) + 1 ≤ equationRank (W i s a) := by omega
      have ht := adaptiveCode_lt W next n (i+1) (next i s (W i s b)) b
      have hstrict : adaptiveCode W next (n+1) i s b < adaptiveCode W next (n+1) i s a := by
        simp only [adaptiveCode]
        nlinarith
      exact ⟨hstrict.le,fun he => (hstrict.ne he).elim⟩

end QuarticPowerFree

open scoped BigOperators

namespace QuarticPowerFree

theorem sum_subsets_erase {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (P : Finset α) (t : ℕ) (f : Finset α → α → M) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, f (S.erase q) q) =
      ∑ B ∈ P.powersetCard t, ∑ q ∈ P \ B, f B q := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun y _ => ⟨y.1.erase y.2, y.2⟩)
  · intro y hy
    obtain ⟨hS, hq⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hSP, hScard⟩ := Finset.mem_powersetCard.mp hS
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨(Finset.erase_subset _ _).trans hSP,
        by rw [Finset.card_erase_of_mem hq, hScard]; omega⟩
    · exact Finset.mem_sdiff.mpr ⟨hSP hq, Finset.notMem_erase _ _⟩
  · intro y hy z hz heq
    have hq : y.2 = z.2 := congrArg Sigma.snd heq
    have hS : y.1.erase y.2 = z.1.erase z.2 := congrArg Sigma.fst heq
    have hyq := (Finset.mem_sigma.mp hy).2
    have hzq := (Finset.mem_sigma.mp hz).2
    have : y.1 = z.1 := by
      calc
        y.1 = insert y.2 (y.1.erase y.2) := (Finset.insert_erase hyq).symm
        _ = insert z.2 (z.1.erase z.2) := by rw [hS, hq]
        _ = z.1 := Finset.insert_erase hzq
    exact Sigma.ext this (heq_of_eq hq)
  · intro y hy
    obtain ⟨hB, hq⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hBP, hBcard⟩ := Finset.mem_powersetCard.mp hB
    obtain ⟨hqP, hqB⟩ := Finset.mem_sdiff.mp hq
    refine ⟨⟨insert y.2 y.1, y.2⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hqP hBP,
          by rw [Finset.card_insert_of_notMem hqB, hBcard]⟩
      · exact Finset.mem_insert_self _ _
    · simp only [Finset.erase_insert hqB]
  · intro y _
    rfl

noncomputable def subsetMean {α : Type*} (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) : ℝ :=
  (∑ S ∈ P.powersetCard t, f S) / (P.powersetCard t).card

theorem subset_incidence_card {α : Type*} [DecidableEq α] (P : Finset α) (t : ℕ) :
    ((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card =
      ((P.card : ℝ) - t) * (P.powersetCard t).card := by
  have h := sum_subsets_erase P t (fun _ _ => (1 : ℝ))
  have hleft : (∑ S ∈ P.powersetCard (t + 1), ∑ _q ∈ S, (1 : ℝ)) =
      ((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card := by
    have heq : ∀ S ∈ P.powersetCard (t + 1), (∑ _q ∈ S, (1 : ℝ)) = (t + 1 : ℕ) := by
      intro S hS
      simp [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hright : (∑ B ∈ P.powersetCard t, ∑ _q ∈ P \ B, (1 : ℝ)) =
      ((P.card : ℝ) - t) * (P.powersetCard t).card := by
    have heq : ∀ B ∈ P.powersetCard t, (∑ _q ∈ P \ B, (1 : ℝ)) = (P.card : ℝ) - t := by
      intro B hB
      obtain ⟨hBP, hBt⟩ := Finset.mem_powersetCard.mp hB
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hBP, hBt]
      exact Nat.cast_sub (hBt ▸ Finset.card_le_card hBP)
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hleft, hright] at h
  exact h

theorem sum_subsets_members {α : Type*} (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard t, ∑ _q ∈ S, f S) =
      (t : ℝ) * ∑ S ∈ P.powersetCard t, f S := by
  have heq : ∀ S ∈ P.powersetCard t, (∑ _q ∈ S, f S) = (t : ℝ) * f S := by
    intro S hS
    simp only [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl heq, Finset.mul_sum]

theorem sum_subsets_complement {α : Type*} [DecidableEq α] (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard t, ∑ _q ∈ P \ S, f S) =
      ((P.card : ℝ) - t) * ∑ S ∈ P.powersetCard t, f S := by
  have heq : ∀ S ∈ P.powersetCard t, (∑ _q ∈ P \ S, f S) = ((P.card : ℝ) - t) * f S := by
    intro S hS
    obtain ⟨hSP, hSt⟩ := Finset.mem_powersetCard.mp hS
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hSP, hSt,
      Nat.cast_sub (hSt ▸ Finset.card_le_card hSP)]
  rw [Finset.sum_congr rfl heq, Finset.mul_sum]

theorem subset_deletion_mean {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (ht : t < P.card) (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, f (S.erase q)) /
        (((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card) = subsetMean P t f := by
  rw [sum_subsets_erase P t (fun S _ => f S), sum_subsets_complement,
    subset_incidence_card, subsetMean]
  exact mul_div_mul_left _ _ (sub_ne_zero.mpr (ne_of_gt (Nat.cast_lt.mpr ht)))

theorem subset_marked_mean {α : Type*} (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ _q ∈ S, f S) /
        (((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card) = subsetMean P (t + 1) f := by
  rw [sum_subsets_members, subsetMean]
  exact mul_div_mul_left _ _ (by positivity)

noncomputable def badFraction {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (bad : Finset α → Finset α) : ℝ :=
  (∑ S ∈ P.powersetCard t, ∑ q ∈ S, if q ∈ bad S then (1 : ℝ) else 0) /
    ((t : ℝ) * (P.powersetCard t).card)

theorem bad_indicator_le_rank_drop {α : Type*} [DecidableEq α]
    (R : Finset α → ℕ) (bad : Finset α → Finset α)
    (S : Finset α) (q : α)
    (hmono : R S ≤ R (S.erase q))
    (hstable : R S = R (S.erase q) → bad S = bad (S.erase q)) :
    (if q ∈ bad S then (1 : ℝ) else 0) ≤
      ((R (S.erase q) : ℝ) - R S) + if q ∈ bad (S.erase q) then 1 else 0 := by
  by_cases heq : R S = R (S.erase q)
  · rw [hstable heq, heq, sub_self, zero_add]
  · have hle : R S + 1 ≤ R (S.erase q) := by omega
    have hle' : (R S : ℝ) + 1 ≤ R (S.erase q) := by exact_mod_cast hle
    split_ifs <;> linarith

theorem deleted_bad_sum_le {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (bad : Finset α → Finset α) (D : ℕ)
    (hbad : ∀ S ⊆ P, (P ∩ bad S).card ≤ D) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S,
      if q ∈ bad (S.erase q) then (1 : ℝ) else 0) ≤
        (P.powersetCard t).card * (D : ℝ) := by
  rw [sum_subsets_erase P t (fun S q => if q ∈ bad S then (1 : ℝ) else 0)]
  calc
    _ ≤ ∑ S ∈ P.powersetCard t, (D : ℝ) := by
      apply Finset.sum_le_sum
      intro S hS
      rw [Finset.sum_boole]
      apply Nat.cast_le.mpr
      apply le_trans (Finset.card_le_card ?_) (hbad S (Finset.mem_powersetCard.mp hS).1)
      intro q hq
      obtain ⟨hqP, hqbad⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hqP).1, hqbad⟩
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem deletion_one_step {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (ht : t < P.card)
    (R : Finset α → ℕ) (bad : Finset α → Finset α) (D : ℕ)
    (hmono : ∀ S ⊆ P, ∀ q ∈ S, R S ≤ R (S.erase q))
    (hstable : ∀ S ⊆ P, ∀ q ∈ S, R S = R (S.erase q) → bad S = bad (S.erase q))
    (hbad : ∀ S ⊆ P, (P ∩ bad S).card ≤ D) :
    badFraction P (t + 1) bad ≤
      subsetMean P t (fun S => R S) - subsetMean P (t + 1) (fun S => R S) +
        (D : ℝ) / ((P.card : ℝ) - t) := by
  have hcard : 0 < (P.powersetCard (t + 1)).card :=
    Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by omega))
  have hsmall : 0 < (P.powersetCard t).card :=
    Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by omega))
  have hden : 0 < ((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card :=
    mul_pos (by positivity) (Nat.cast_pos.mpr hcard)
  have hsum :
      (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, if q ∈ bad S then (1 : ℝ) else 0) ≤
      (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, (R (S.erase q) : ℝ)) -
      (∑ S ∈ P.powersetCard (t + 1), ∑ _q ∈ S, (R S : ℝ)) +
      (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S,
        if q ∈ bad (S.erase q) then (1 : ℝ) else 0) := by
    simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S hS
    apply Finset.sum_le_sum
    intro q hq
    exact bad_indicator_le_rank_drop R bad S q
      (hmono S (Finset.mem_powersetCard.mp hS).1 q hq)
      (hstable S (Finset.mem_powersetCard.mp hS).1 q hq)
  have hsum' := div_le_div_of_nonneg_right hsum hden.le
  rw [add_div, sub_div, subset_deletion_mean P t ht (fun S => (R S : ℝ)),
    subset_marked_mean P t (fun S => (R S : ℝ))] at hsum'
  have hbad' := div_le_div_of_nonneg_right (deleted_bad_sum_le P t bad D hbad) hden.le
  have herr : ((P.powersetCard t).card * (D : ℝ)) /
      (((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card) =
        (D : ℝ) / ((P.card : ℝ) - t) := by
    rw [subset_incidence_card, mul_comm ((P.card : ℝ) - t)]
    exact mul_div_mul_left _ _ (ne_of_gt (Nat.cast_pos.mpr hsmall))
  rw [herr] at hbad'
  change _ ≤ _ at hsum'
  dsimp only [badFraction]
  linarith

theorem subsetMean_record_bounds {α : Type*}
    (P : Finset α) (t : ℕ) (ht : t ≤ P.card)
    (R : Finset α → ℕ) (B : ℕ) (hR : ∀ S ⊆ P, R S ≤ B) :
    0 ≤ subsetMean P t (fun S => R S) ∧ subsetMean P t (fun S => R S) ≤ B := by
  have hcard : 0 < (P.powersetCard t).card :=
    Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr ht)
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun S _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · rw [subsetMean, div_le_iff₀ (Nat.cast_pos.mpr hcard)]
    calc
      _ ≤ ∑ _S ∈ P.powersetCard t, (B : ℝ) := by
        apply Finset.sum_le_sum
        intro S hS
        exact Nat.cast_le.mpr (hR S (Finset.mem_powersetCard.mp hS).1)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem deletion_average_bound {α : Type*} [DecidableEq α]
    (P : Finset α) (ell T : ℕ) (hT : 0 < T) (hsize : ell + T < P.card)
    (R : Finset α → ℕ) (bad : Finset α → Finset α) (B D : ℕ)
    (hR : ∀ S ⊆ P, R S ≤ B)
    (hmono : ∀ S ⊆ P, ∀ q ∈ S, R S ≤ R (S.erase q))
    (hstable : ∀ S ⊆ P, ∀ q ∈ S, R S = R (S.erase q) → bad S = bad (S.erase q))
    (hbad : ∀ S ⊆ P, (P ∩ bad S).card ≤ D) :
    (∑ j ∈ Finset.range T, badFraction P (ell + j + 1) bad) / (T : ℝ) ≤
      (B : ℝ) / T + (D : ℝ) / ((P.card : ℝ) - (ell + T)) := by
  let F : ℕ → ℝ := fun j => subsetMean P (ell + j) (fun S => R S)
  let err : ℝ := (D : ℝ) / ((P.card : ℝ) - (ell + T))
  have hgap : 0 < (P.card : ℝ) - (ell + T) := by
    apply sub_pos.mpr
    exact_mod_cast hsize
  have hstep (j : ℕ) (hj : j ∈ Finset.range T) :
      badFraction P (ell + j + 1) bad ≤ F j - F (j + 1) + err := by
    have hjt := Finset.mem_range.mp hj
    have ht : ell + j < P.card := by omega
    have h := deletion_one_step P (ell + j) ht R bad D hmono hstable hbad
    have herr : (D : ℝ) / ((P.card : ℝ) - (ell + j)) ≤ err := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hgap
      have : (j : ℝ) ≤ T := by exact_mod_cast (Nat.le_of_lt hjt)
      linarith
    dsimp [F]
    simp only [Nat.add_assoc, Nat.cast_add] at h ⊢
    exact h.trans (by linarith)
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  have hupper := (subsetMean_record_bounds P ell (by omega) R B hR).2
  have hlower := (subsetMean_record_bounds P (ell + T) (by omega) R B hR).1
  have hdiff : F 0 - F T ≤ (B : ℝ) := by
    dsimp [F]
    simpa only [Nat.add_zero] using sub_le_self _ hlower |>.trans hupper
  have hsum' : (∑ j ∈ Finset.range T, badFraction P (ell + j + 1) bad) ≤
      (B : ℝ) + T * err := by linarith
  have hT' : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  calc
    _ ≤ ((B : ℝ) + T * err) / T := div_le_div_of_nonneg_right hsum' hT'.le
    _ = (B : ℝ) / T + err := by rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hT')]
    _ = _ := rfl

end QuarticPowerFree

end OAI

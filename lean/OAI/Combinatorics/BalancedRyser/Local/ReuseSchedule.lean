import OAI.Combinatorics.BalancedRyser.Local.ReuseOrdering
import OAI.Combinatorics.BalancedRyser.Probability.PatternMoments

namespace OAI

namespace Balanced.ReuseSchedule

open scoped BigOperators

noncomputable section
open scoped Classical

variable {A J : Type*} [Fintype A] [Fintype J] [DecidableEq J]

theorem sum_category_weight (category : A → J) (cost : J → ℝ) (W : A → ℝ) :
    (∑ a, cost (category a) * W a) =
      ∑ j, cost j * (∑ a, if category a = j then W a else 0) := by
  classical
  calc
    (∑ a, cost (category a) * W a) =
        ∑ a, ∑ j, if category a = j then cost j * W a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ j, cost j * (∑ a, if category a = j then W a else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp

theorem weighted_step_le (W : List A → ℝ) (score : List A → ℕ)
    (category : List A → A → J) (saving : J → ℕ)
    (q C : ℝ) (hq : 0 < q) (pre : List A)
    (hscore : ∀ a, score (a :: pre) = score pre + saving (category pre a))
    (hstep : ∀ j, (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
      (C / q ^ saving j) * W pre) :
    (∑ a, q ^ score (a :: pre) * W (a :: pre)) ≤
      ((Fintype.card J : ℝ) * C) * (q ^ score pre * W pre) := by
  classical
  calc
    (∑ a, q ^ score (a :: pre) * W (a :: pre)) =
        q ^ score pre * ∑ a, q ^ saving (category pre a) * W (a :: pre) := by
      simp_rw [hscore, pow_add]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = q ^ score pre * ∑ j,
        q ^ saving j * (∑ a, if category pre a = j then W (a :: pre) else 0) := by
      rw [sum_category_weight (category pre) (fun j => q ^ saving j)
        (fun a => W (a :: pre))]
    _ ≤ q ^ score pre * ∑ _j : J, C * W pre := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq.le _)
      apply Finset.sum_le_sum
      intro j _
      calc
        q ^ saving j * (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
            q ^ saving j * ((C / q ^ saving j) * W pre) :=
          mul_le_mul_of_nonneg_left (hstep j) (pow_nonneg hq.le _)
        _ = C * W pre := by
          field_simp
    _ = ((Fintype.card J : ℝ) * C) * (q ^ score pre * W pre) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

omit [Fintype A] in
private theorem scheduleAllowed_all_true
    (overlap : List A → A → Prop) (n : ℕ) (labels pre : List A) :
    PatternMoments.scheduleAllowed overlap (List.replicate n true) labels pre ↔
      labels.length = n := by
  induction n generalizing labels pre with
  | zero => cases labels <;> simp [PatternMoments.scheduleAllowed]
  | succ n ih =>
      cases labels with
      | nil => simp [PatternMoments.scheduleAllowed]
      | cons a labels =>
          simpa [List.replicate_succ, PatternMoments.scheduleAllowed] using ih labels (a :: pre)

private theorem scheduleCost_all_true (C L : ℝ) (n : ℕ) :
    PatternMoments.scheduleCost C L (List.replicate n true) = C ^ n := by
  induction n with
  | zero => simp [PatternMoments.scheduleCost]
  | succ n ih => simp [List.replicate_succ, PatternMoments.scheduleCost, ih, pow_succ, mul_comm]

theorem sum_words_le (W : List A → ℝ) (N n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ pre, pre.length < N → (∑ a, W (a :: pre)) ≤ C * W pre)
    (pre : List A) (hlen : pre.length + n ≤ N) :
    (∑ a : Fin n → A, W ((List.ofFn a).reverse ++ pre)) ≤ C ^ n * W pre := by
  classical
  let overlap : List A → A → Prop := fun _ _ => False
  have hexpand := PatternMoments.scheduledWeight_eq_sum_of_length W overlap
    (List.replicate n true) pre n (List.length_replicate ..)
  have hallowed (a : Fin n → A) : PatternMoments.scheduleAllowed overlap
      (List.replicate n true) (List.ofFn a) pre :=
    (scheduleAllowed_all_true overlap n (List.ofFn a) pre).mpr (List.length_ofFn ..)
  simp only [hallowed, ite_true] at hexpand
  rw [← hexpand]
  have h := PatternMoments.scheduledWeight_le W overlap N C 0 hC le_rfl hstep
    (by intro pre _; simp [overlap]) (List.replicate n true) pre
    (by simpa using hlen)
  simpa only [scheduleCost_all_true] using h

theorem sum_weighted_words_le (W : List A → ℝ) (score : List A → ℕ)
    (category : List A → A → J) (saving : J → ℕ)
    (N n : ℕ) (q C : ℝ) (hq : 0 < q) (hC : 0 ≤ C)
    (hscore : ∀ pre a, score (a :: pre) = score pre + saving (category pre a))
    (hstep : ∀ pre, pre.length < N → ∀ j,
      (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
        (C / q ^ saving j) * W pre)
    (pre : List A) (hlen : pre.length + n ≤ N) :
    (∑ a : Fin n → A,
      q ^ score ((List.ofFn a).reverse ++ pre) * W ((List.ofFn a).reverse ++ pre)) ≤
      ((Fintype.card J : ℝ) * C) ^ n * (q ^ score pre * W pre) := by
  apply sum_words_le (fun l => q ^ score l * W l) N n
    ((Fintype.card J : ℝ) * C) (mul_nonneg (Nat.cast_nonneg _) hC) _ pre hlen
  intro pre hpre
  exact weighted_step_le W score category saving q C hq pre (hscore pre)
    (hstep pre hpre)

theorem sum_high_score_words_le (W : List A → ℝ) (score : List A → ℕ)
    (category : List A → A → J) (saving : J → ℕ)
    (N n m : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hW : ∀ pre, 0 ≤ W pre) (hzero : score [] = 0)
    (hscore : ∀ pre a, score (a :: pre) = score pre + saving (category pre a))
    (hstep : ∀ pre, pre.length < N → ∀ j,
      (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
        (C / q ^ saving j) * W pre)
    (hlen : n ≤ N) :
    (∑ a : Fin n → A, if m ≤ score (List.ofFn a).reverse then
      W (List.ofFn a).reverse else 0) ≤
      ((Fintype.card J : ℝ) * C) ^ n * W [] / q ^ m := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  apply (le_div_iff₀ (pow_pos hqpos m)).mpr
  calc
    (∑ a : Fin n → A, if m ≤ score (List.ofFn a).reverse then
        W (List.ofFn a).reverse else 0) * q ^ m ≤
        ∑ a : Fin n → A,
          q ^ score (List.ofFn a).reverse * W (List.ofFn a).reverse := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro a _
      by_cases hs : m ≤ score (List.ofFn a).reverse
      · rw [ite_eq_left hs, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq hs) (hW _)
      · rw [ite_eq_right hs, zero_mul]
        exact mul_nonneg (pow_nonneg hqpos.le _) (hW _)
    _ ≤ ((Fintype.card J : ℝ) * C) ^ n * W [] := by
      have h := sum_weighted_words_le W score category saving N n q C hqpos hC
        hscore hstep [] (by simpa using hlen)
      simpa only [List.append_nil, hzero, pow_zero, one_mul] using h

theorem sum_reuse_witness_weights_le {D : Type*} [DecidableEq A] [DecidableEq D]
    (G : A → Finset D) (hfour : ∀ a, (G a).card ≤ 4)
    (W : List A → ℝ) (N n m : ℕ) (q C : ℝ) (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hW : ∀ pre, 0 ≤ W pre)
    (hstep : ∀ pre, pre.length < N → ∀ j : ℕ, j ≤ 4 →
      (∑ a, if (G a ∩ pre.toFinset.biUnion G).card = j then W (a :: pre) else 0) ≤
        (C / q ^ reuseSaving j) * W pre)
    (hlen : n ≤ N) :
    (∑ a : Fin n → A, if m ≤ reuseExposureScore G (List.ofFn a).reverse then
      W (List.ofFn a).reverse else 0) ≤ (5 * C) ^ n * W [] / q ^ m := by
  classical
  let category : List A → A → Fin 5 := fun pre a =>
    ⟨(G a ∩ pre.toFinset.biUnion G).card, by
      have h := (Finset.card_le_card (Finset.inter_subset_left :
        G a ∩ pre.toFinset.biUnion G ⊆ G a)).trans (hfour a)
      omega⟩
  have hstep' (pre : List A) (hp : pre.length < N) (j : Fin 5) :
      (∑ a, if category pre a = j then W (a :: pre) else 0) ≤
        (C / q ^ reuseSaving j.val) * W pre := by
    simpa only [category, Fin.ext_iff] using hstep pre hp j.val (by omega)
  have h := sum_high_score_words_le W (reuseExposureScore G) category
    (fun j : Fin 5 => reuseSaving j.val) N n m q C hq hC hW rfl
    (fun _ _ => rfl) (by
      intro pre hp j
      simpa only using hstep' pre hp j) hlen
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

end
end Balanced.ReuseSchedule

end OAI

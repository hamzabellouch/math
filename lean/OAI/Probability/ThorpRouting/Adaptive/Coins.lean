import Mathlib
import OAI.Probability.ThorpRouting.Adaptive.Model

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

open scoped BigOperators
open Filter

def Coins : ℕ → Type
  | 0 => Unit
  | d + 1 => Card d → Bool

instance (d : ℕ) : Fintype (Coins d) := by
  cases d <;> dsimp [Coins] <;> infer_instance

instance (d : ℕ) : Nonempty (Coins d) := by
  cases d <;> dsimp [Coins] <;> infer_instance

def rotate (d : ℕ) : Equiv.Perm (Card d) where
  toFun x i := x (finRotate d i)
  invFun x i := x ((finRotate d).symm i)
  left_inv x := by funext i; simp only [Equiv.apply_symm_apply]
  right_inv x := by funext i; simp only [Equiv.symm_apply_apply]

def step : (d : ℕ) → Coins d → Equiv.Perm (Card d)
  | 0, _ => 1
  | d + 1, ξ => rotate (d + 1) * pairSwitch ξ

def run (d : ℕ) : (t : ℕ) → (Fin t → Coins d) → Equiv.Perm (Card d)
  | 0, _ => 1
  | t + 1, ω => step d (ω (Fin.last t)) * run d t (fun i => ω i.castSucc)

noncomputable def law (d t : ℕ) (g : Equiv.Perm (Card d)) : ℝ :=
  (Fintype.card {ω : Fin t → Coins d // run d t ω = g} : ℝ) /
    (Fintype.card (Fin t → Coins d) : ℝ)

noncomputable def distance (d t : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ g : Equiv.Perm (Card d),
    |law d t g - 1 / (Nat.factorial (2 ^ d) : ℝ)|

noncomputable def mixingTime (d : ℕ) : ℕ :=
  sInf {t : ℕ | distance d t ≤ (1 / 4 : ℝ)}

noncomputable def supportTimeBound (d : ℕ) : ℤ :=
  ⌈(2 / (2 : ℝ) ^ d) *
    (Real.log ((3 / 4 : ℝ) * (Nat.factorial (2 ^ d) : ℝ)) / Real.log 2)⌉

def OptimalOrder : Prop :=
  ∃ C : ℕ, 0 < C ∧
    Tendsto (fun d : ℕ => distance d (C * d)) atTop (nhds 0) ∧
    (∀ d t : ℕ, 1 - (2 : ℝ) ^ ((t : ℝ) * (2 : ℝ) ^ d / 2) /
      (Nat.factorial (2 ^ d) : ℝ) ≤ distance d t) ∧
    (∀ᶠ d : ℕ in atTop,
      supportTimeBound d ≤ (mixingTime d : ℤ) ∧ mixingTime d ≤ C * d) ∧
    (∃ K : ℝ, ∀ᶠ d : ℕ in atTop, 2 * (d : ℝ) - K ≤ (mixingTime d : ℝ)) ∧
    Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ)) (fun d : ℕ => (d : ℝ))

noncomputable def finiteLaw {α β : Type*} [Fintype α] (f : α → β) (b : β) : ℝ := by
  classical
  exact (Fintype.card {a : α // f a = b} : ℝ) / (Fintype.card α : ℝ)

lemma sum_card_fibers {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) :
    ∑ b, Fintype.card {a : α // f a = b} = Fintype.card α := by
  classical
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

lemma finiteLaw_nonneg {α β : Type*} [Fintype α] (f : α → β) (b : β) :
    0 ≤ finiteLaw f b := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma finiteLaw_sum {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] (f : α → β) :
    ∑ b, finiteLaw f b = 1 := by
  classical
  simp only [finiteLaw, ← Finset.sum_div]
  have hc : (∑ b, (Fintype.card {a : α // f a = b} : ℝ)) = (Fintype.card α : ℝ) := by
    exact_mod_cast sum_card_fibers f
  rw [hc]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma finiteLaw_eq_zero_of_not_mem {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) {b : β} (hb : b ∉ Finset.univ.image f) : finiteLaw f b = 0 := by
  classical
  have : IsEmpty {a : α // f a = b} := ⟨fun a => hb (Finset.mem_image.mpr
    ⟨a.val, Finset.mem_univ _, a.property⟩)⟩
  simp [finiteLaw]

lemma event_le_totalVariation {β : Type*} [Fintype β] [DecidableEq β]
    (p q : β → ℝ) (hpq : ∑ b, (p b - q b) = 0) (s : Finset β) :
    (∑ b ∈ s, p b) - (∑ b ∈ s, q b) ≤ (1 / 2 : ℝ) * ∑ b, |p b - q b| := by
  have h₁ : (∑ b ∈ s, (p b - q b)) ≤ ∑ b ∈ s, |p b - q b| :=
    Finset.sum_le_sum (fun b _ => le_abs_self (p b - q b))
  have h₂ : -(∑ b ∈ sᶜ, (p b - q b)) ≤ ∑ b ∈ sᶜ, |p b - q b| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun b _ => neg_le_abs (p b - q b))
  have hz := Finset.sum_add_sum_compl s (fun b => p b - q b)
  have ha := Finset.sum_add_sum_compl s (fun b => |p b - q b|)
  rw [hpq] at hz
  rw [← Finset.sum_sub_distrib]
  linarith

lemma finiteLaw_support_bound {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (f : α → β) :
    1 - (Fintype.card α : ℝ) / (Fintype.card β : ℝ) ≤
      (1 / 2 : ℝ) * ∑ b, |finiteLaw f b - 1 / (Fintype.card β : ℝ)| := by
  classical
  let s := Finset.univ.image f
  have hs : ∑ b ∈ s, finiteLaw f b = 1 := by
    have h := Finset.sum_subset (Finset.subset_univ s)
      (fun b _ hb => finiteLaw_eq_zero_of_not_mem f hb)
    simpa only [finiteLaw_sum] using h
  have hβ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hq : (∑ _b : β, 1 / (Fintype.card β : ℝ)) = 1 := by simp [hβ]
  have hd : (∑ b, (finiteLaw f b - 1 / (Fintype.card β : ℝ))) = 0 := by
    rw [Finset.sum_sub_distrib, finiteLaw_sum, hq, sub_self]
  have he := event_le_totalVariation (finiteLaw f) (fun _ => 1 / (Fintype.card β : ℝ)) hd s
  rw [hs] at he
  have hsq : (∑ _b ∈ s, 1 / (Fintype.card β : ℝ)) = (s.card : ℝ) / Fintype.card β := by
    simp [div_eq_mul_inv]
  rw [hsq] at he
  have hcard : (s.card : ℝ) ≤ Fintype.card α := by
    exact_mod_cast (Finset.card_image_le (s := (Finset.univ : Finset α)) (f := f))
  have hdiv := div_le_div_of_nonneg_right hcard (Nat.cast_nonneg (Fintype.card β) : (0 : ℝ) ≤ _)
  linarith

lemma card_positions (d : ℕ) : Fintype.card (Card d) = 2 ^ d := by
  simp [Card]

lemma card_permutations (d : ℕ) : Fintype.card (Equiv.Perm (Card d)) = Nat.factorial (2 ^ d) := by
  rw [Fintype.card_perm, card_positions]

lemma card_coins_succ (d : ℕ) : Fintype.card (Coins (d + 1)) = 2 ^ (2 ^ d) := by
  simp [Coins]

lemma card_tapes_succ (d t : ℕ) : Fintype.card (Fin t → Coins (d + 1)) = 2 ^ (t * 2 ^ d) := by
  rw [Fintype.card_fun, card_coins_succ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

lemma law_eq_finiteLaw (d t : ℕ) (g : Equiv.Perm (Card d)) :
    law d t g = finiteLaw (run d t) g := by
  unfold law finiteLaw
  apply congrArg (fun n : ℕ => (n : ℝ) / (Fintype.card (Fin t → Coins d) : ℝ))
  exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)

lemma law_nonneg (d t : ℕ) (g : Equiv.Perm (Card d)) : 0 ≤ law d t g := by
  rw [law_eq_finiteLaw]
  exact finiteLaw_nonneg (run d t) g

lemma law_sum (d t : ℕ) : ∑ g, law d t g = 1 := by
  simp only [law_eq_finiteLaw]
  exact finiteLaw_sum (run d t)

lemma physical_support_bound_succ (d t : ℕ) :
    1 - (2 : ℝ) ^ (t * 2 ^ d) / (Nat.factorial (2 ^ (d + 1)) : ℝ) ≤ distance (d + 1) t := by
  have : Nonempty (Equiv.Perm (Card (d + 1))) := ⟨1⟩
  have h := finiteLaw_support_bound (run (d + 1) t)
  rw [card_tapes_succ, card_permutations] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat, distance, law_eq_finiteLaw] using h

lemma step_succ_formula (d : ℕ) (ξ : Coins (d + 1)) (x : Card (d + 1)) :
    step (d + 1) ξ x = Fin.snoc (Fin.tail x) (Bool.xor (x 0) (ξ (Fin.tail x))) := by
  change (fun i => switchFun ξ x (finRotate (d + 1) i)) = _
  rw [Fin.snoc_eq_cons_rotate]
  rfl

lemma distance_nonneg (d t : ℕ) : 0 ≤ distance d t := by
  unfold distance
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

lemma physical_support_bound (d t : ℕ) :
    1 - (2 : ℝ) ^ ((t : ℝ) * (2 : ℝ) ^ d / 2) /
      (Nat.factorial (2 ^ d) : ℝ) ≤ distance d t := by
  cases d with
  | zero =>
    have h : 1 ≤ (2 : ℝ) ^ ((t : ℝ) / 2) := Real.one_le_rpow (by norm_num) (by positivity)
    simpa only [pow_zero, Nat.factorial_one, Nat.cast_one, div_one, mul_one] using
      le_trans (sub_nonpos.mpr h) (distance_nonneg 0 t)
  | succ d =>
    have he : (t : ℝ) * (2 : ℝ) ^ (d + 1) / 2 = (t * 2 ^ d : ℕ) := by
      push_cast
      rw [pow_succ]
      ring
    rw [he, Real.rpow_natCast]
    exact physical_support_bound_succ d t

lemma supportTimeBound_le_of_distance_le (d t : ℕ) (ht : distance d t ≤ (1 / 4 : ℝ)) :
    supportTimeBound d ≤ (t : ℤ) := by
  have hF : (0 : ℝ) < Nat.factorial (2 ^ d) := by positivity
  have hN : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hb := physical_support_bound d t
  have hp : (3 / 4 : ℝ) ≤
      (2 : ℝ) ^ ((t : ℝ) * (2 : ℝ) ^ d / 2) / (Nat.factorial (2 ^ d) : ℝ) := by
    linarith
  have hr := (le_div_iff₀ hF).mp hp
  have hlog := Real.log_le_log (show (0 : ℝ) < (3 / 4 : ℝ) * Nat.factorial (2 ^ d) by positivity) hr
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  unfold supportTimeBound
  apply Int.ceil_le.mpr
  simp only [Int.cast_natCast]
  calc
    2 / (2 : ℝ) ^ d * (Real.log ((3 / 4 : ℝ) * Nat.factorial (2 ^ d)) / Real.log 2) =
        Real.log ((3 / 4 : ℝ) * Nat.factorial (2 ^ d)) / ((2 : ℝ) ^ d / 2 * Real.log 2) := by
      field_simp
    _ ≤ (t : ℝ) := (div_le_iff₀ (mul_pos (div_pos hN (by norm_num)) hL)).mpr (by
      nlinarith [hlog])

lemma supportTimeBound_le_mixingTime {d : ℕ}
    (h : ({t : ℕ | distance d t ≤ (1 / 4 : ℝ)} : Set ℕ).Nonempty) :
    supportTimeBound d ≤ (mixingTime d : ℤ) := by
  exact supportTimeBound_le_of_distance_le d (mixingTime d) (Nat.sInf_mem h)

lemma log_factorial_lower {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (Nat.factorial n) := by
  have h := Stirling.le_log_factorial_stirling (show n ≠ 0 by omega)
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlp : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by
    have := Real.pi_gt_three
    linarith)
  linarith

lemma log_three_quarters_lower : -(1 : ℝ) ≤ Real.log (3 / 4 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  have he : Real.log (4 / 3 : ℝ) = - Real.log (3 / 4 : ℝ) := by
    rw [← Real.log_inv]
    congr 1
    norm_num
  rw [he] at h
  linarith

lemma linear_le_supportTimeBound (d : ℕ) :
    2 * (d : ℝ) - 4 / Real.log 2 ≤ (supportTimeBound d : ℝ) := by
  have hN : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hNp : 0 < (2 : ℝ) ^ d := by positivity
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf := log_factorial_lower (show 1 ≤ 2 ^ d by exact one_le_pow₀ (by norm_num))
  have hlog : (2 : ℝ) ^ d * ((d : ℝ) * Real.log 2) - (2 : ℝ) ^ d - 1 ≤
      Real.log ((3 / 4 : ℝ) * (Nat.factorial (2 ^ d) : ℝ)) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    push_cast at hf
    rw [Real.log_pow] at hf
    linarith [log_three_quarters_lower]
  apply le_trans _ (Int.le_ceil _)
  have hmul : (2 * (d : ℝ) - 4 / Real.log 2) *
      ((2 : ℝ) ^ d / 2 * Real.log 2) ≤
      Real.log ((3 / 4 : ℝ) * (Nat.factorial (2 ^ d) : ℝ)) := by
    have hcancel : (2 * (d : ℝ) - 4 / Real.log 2) *
        ((2 : ℝ) ^ d / 2 * Real.log 2) =
        (2 : ℝ) ^ d * ((d : ℝ) * Real.log 2) - 2 * (2 : ℝ) ^ d := by
      field_simp
      ring
    rw [hcancel]
    linarith
  convert (le_div_iff₀ (mul_pos (div_pos hNp (by norm_num)) hL)).mpr hmul using 1
  field_simp

lemma linear_le_time_of_distance_le (d t : ℕ)
    (ht : distance d t ≤ (1 / 4 : ℝ)) :
    2 * (d : ℝ) - 4 / Real.log 2 ≤ (t : ℝ) := by
  have h := supportTimeBound_le_of_distance_le d t ht
  have hr : (supportTimeBound d : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
  exact (linear_le_supportTimeBound d).trans hr

lemma entropy_chord (p : ℝ) (hp : 0 ≤ p) (hq : p ≤ 1 / 2) :
    2 * p * Real.log 2 ≤ Real.binEntropy p := by
  have hc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show (2 : ℝ)⁻¹ ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show 0 ≤ 1 - 2 * p by linarith)
    (show 0 ≤ 2 * p by positivity)
    (show (1 - 2 * p) + 2 * p = 1 by ring)
  simpa only [Real.binEntropy_zero, Real.binEntropy_two_inv,
    smul_eq_mul, mul_zero, zero_add, show 2 * p * (2 : ℝ)⁻¹ = p by ring] using hc

lemma split_entropy_lower (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * min a b * Real.log 2 ≤
      (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b := by
  wlog hab : a ≤ b generalizing a b
  · have hba := this b a hb ha (le_of_not_ge hab)
    simpa only [min_comm, add_comm b a] using hba.trans_eq (show (b + a) * Real.log (b + a) - b * Real.log b - a * Real.log a =
      (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b by rw [add_comm b a]; ring)
  rw [min_eq_left hab]
  by_cases hz : a = 0
  · subst a
    simp
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  have hbp : 0 < b := hap.trans_le hab
  have hs : 0 < a + b := add_pos hap hbp
  have hp : 0 ≤ a / (a + b) := div_nonneg ha hs.le
  have hq : a / (a + b) ≤ 1 / 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hc := mul_le_mul_of_nonneg_left (entropy_chord (a / (a + b)) hp hq) hs.le
  have he : (a + b) * Real.binEntropy (a / (a + b)) =
      (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b := by
    unfold Real.binEntropy
    rw [show 1 - a / (a + b) = b / (a + b) by field_simp; ring]
    simp only [Real.log_inv]
    rw [Real.log_div (ne_of_gt hap) (ne_of_gt hs),
      Real.log_div (ne_of_gt hbp) (ne_of_gt hs)]
    field_simp
    ring
  rw [he] at hc
  calc
    2 * a * Real.log 2 = (a + b) * (2 * (a / (a + b)) * Real.log 2) := by
      field_simp
    _ ≤ _ := hc

noncomputable def childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) :
    Finset (Card d) := (s.filter (fun x => x 0 = ε)).image Fin.tail

lemma card_childMarks {d : ℕ} (s : Finset (Card (d + 1))) (ε : Bool) :
    (childMarks s ε).card = (s.filter (fun x => x 0 = ε)).card := by
  classical
  unfold childMarks
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  have hx0 := (Finset.mem_filter.mp hx).2
  have hy0 := (Finset.mem_filter.mp hy).2
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hx0, hy0, hxy]

lemma card_childMarks_add {d : ℕ} (s : Finset (Card (d + 1))) :
    (childMarks s false).card + (childMarks s true).card = s.card := by
  classical
  rw [card_childMarks, card_childMarks]
  simpa only [Bool.not_eq_false] using
    (Finset.card_filter_add_card_filter_not (s := s) (fun x => x 0 = false))

noncomputable def topMeetings {d : ℕ} (b : Butterfly (d + 1))
    (s : Finset (Card (d + 1))) : Finset (Card d) :=
  ((childMarks s false).image (butterflyPerm d (b.2 false))) ∩
    ((childMarks s true).image (butterflyPerm d (b.2 true)))

lemma card_topMeetings_le {d : ℕ} (b : Butterfly (d + 1)) (s : Finset (Card (d + 1))) :
    (topMeetings b s).card ≤ min (childMarks s false).card (childMarks s true).card := by
  classical
  apply le_min
  · exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (Finset.card_image_of_injective _ (butterflyPerm d (b.2 false)).injective)
  · exact (Finset.card_le_card Finset.inter_subset_right).trans_eq
      (Finset.card_image_of_injective _ (butterflyPerm d (b.2 true)).injective)

noncomputable def encounters : (d : ℕ) → Butterfly d → Finset (Card d) → ℕ
  | 0, _, _ => 0
  | d + 1, b, s => encounters d (b.2 false) (childMarks s false) +
      encounters d (b.2 true) (childMarks s true) + (topMeetings b s).card

lemma butterfly_encounters (d : ℕ) (b : Butterfly d) (s : Finset (Card d)) :
    (encounters d b s : ℝ) ≤ (s.card : ℝ) * Real.log s.card / (2 * Real.log 2) := by
  induction d with
  | zero =>
    simp only [encounters, Nat.cast_zero]
    have hs : s.card ≤ 1 := by
      simpa [Card] using Finset.card_le_univ s
    interval_cases s.card <;> simp
  | succ d ih =>
    have h₀ := ih (b.2 false) (childMarks s false)
    have h₁ := ih (b.2 true) (childMarks s true)
    have ht : ((topMeetings b s).card : ℝ) ≤
        min ((childMarks s false).card : ℝ) ((childMarks s true).card : ℝ) := by
      exact_mod_cast card_topMeetings_le b s
    have he := split_entropy_lower ((childMarks s false).card : ℝ)
      ((childMarks s true).card : ℝ) (by positivity) (by positivity)
    have hs : ((childMarks s false).card : ℝ) + (childMarks s true).card = s.card := by
      exact_mod_cast card_childMarks_add s
    rw [hs] at he
    have hL : 0 < 2 * Real.log 2 := by positivity
    rw [le_div_iff₀ hL] at h₀ h₁ ⊢
    simp only [encounters, Nat.cast_add]
    nlinarith [mul_le_mul_of_nonneg_right ht hL.le]

lemma prod_split_at {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ) (a : α) :
    ∏ i ∈ s, f i = (if a ∈ s then f a else 1) * ∏ i ∈ s.erase a, f i := by
  by_cases ha : a ∈ s
  · rw [ite_eq_left ha]
    exact (Finset.mul_prod_erase s f ha).symm
  · simp [ha]

lemma prod_split_two {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (a b : α) (hab : a ≠ b) :
    ∏ i ∈ s, f i = (if a ∈ s then f a else 1) * (if b ∈ s then f b else 1) *
      ∏ i ∈ (s.erase a).erase b, f i := by
  calc
    ∏ i ∈ s, f i = (if a ∈ s then f a else 1) * ∏ i ∈ s.erase a, f i :=
      prod_split_at s f a
    _ = _ := by
      rw [prod_split_at (s.erase a) f b]
      have hm : (b ∈ s.erase a) ↔ b ∈ s :=
        ⟨fun h => (Finset.mem_erase.mp h).2, fun h => Finset.mem_erase.mpr ⟨Ne.symm hab, h⟩⟩
      simp only [hm, mul_assoc]

lemma swap_average_product {α : Type*} [DecidableEq α] (s : Finset α) (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (a b : α) :
    ((∏ i ∈ s, p i) + ∏ i ∈ s, p (Equiv.swap a b i)) / 2 ≤
      ∏ i ∈ s, (p i + p (Equiv.swap a b i)) / 2 := by
  by_cases hab : a = b
  · subst b
    simp only [Equiv.swap_self, Equiv.refl_apply]
    have h : (fun i => (p i + p i) / 2) = p := by funext i; ring
    rw [h]
    linarith
  let t := (s.erase a).erase b
  have hfix : ∀ i ∈ t, Equiv.swap a b i = i := by
    intro i hi
    exact Equiv.swap_apply_of_ne_of_ne (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      (Finset.mem_erase.mp hi).1
  have hprod : (∏ i ∈ t, p (Equiv.swap a b i)) = ∏ i ∈ t, p i :=
    Finset.prod_congr rfl (fun i hi => by rw [hfix i hi])
  have havg : (∏ i ∈ t, (p i + p (Equiv.swap a b i)) / 2) = ∏ i ∈ t, p i :=
    Finset.prod_congr rfl (fun i hi => by rw [hfix i hi]; ring)
  rw [prod_split_two s p a b hab,
    prod_split_two s (fun i => p (Equiv.swap a b i)) a b hab,
    prod_split_two s (fun i => (p i + p (Equiv.swap a b i)) / 2) a b hab]
  change ((if a ∈ s then p a else 1) * (if b ∈ s then p b else 1) * (∏ i ∈ t, p i) +
    (if a ∈ s then p (Equiv.swap a b a) else 1) *
      (if b ∈ s then p (Equiv.swap a b b) else 1) * (∏ i ∈ t, p (Equiv.swap a b i))) / 2 ≤ _
  rw [hprod]
  change _ ≤ (if a ∈ s then (p a + p (Equiv.swap a b a)) / 2 else 1) *
    (if b ∈ s then (p b + p (Equiv.swap a b b)) / 2 else 1) *
      (∏ i ∈ t, (p i + p (Equiv.swap a b i)) / 2)
  rw [havg, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have ht : 0 ≤ ∏ i ∈ t, p i := Finset.prod_nonneg (fun i _ => hp i)
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> simp only [ha, hb, ↓reduceIte]
  · have hsq := mul_nonneg (sq_nonneg (p a - p b)) ht
    nlinarith
  all_goals ring_nf; rfl

def CylinderBound {α : Type*} (m : Finset α → ℝ) (p : α → ℝ) : Prop :=
  ∀ s, m s ≤ ∏ i ∈ s, p i

lemma CylinderBound.fair_swap {α : Type*} [DecidableEq α]
    {m : Finset α → ℝ} {p : α → ℝ} (h : CylinderBound m p)
    (hp : ∀ i, 0 ≤ p i) (a b : α) :
    CylinderBound (fun s => (m s + m (s.image (Equiv.swap a b))) / 2)
      (fun i => (p i + p (Equiv.swap a b i)) / 2) := by
  intro s
  have h₀ := h s
  have h₁ := h (s.image (Equiv.swap a b))
  rw [Finset.prod_image (Equiv.swap a b).injective.injOn] at h₁
  exact (show (m s + m (s.image (Equiv.swap a b))) / 2 ≤
      ((∏ i ∈ s, p i) + ∏ i ∈ s, p (Equiv.swap a b i)) / 2 by linarith).trans
    (swap_average_product s p hp a b)

noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

noncomputable def inclusionMoment {α Ω : Type*} [Fintype Ω]
    (F : Ω → Finset α) (s : Finset α) : ℝ := by
  classical
  exact finiteMean (fun ω => if s ⊆ F ω then 1 else 0)

lemma inclusionMoment_nonneg {α Ω : Type*} [Fintype Ω]
    (F : Ω → Finset α) (s : Finset α) : 0 ≤ inclusionMoment F s := by
  classical
  unfold inclusionMoment finiteMean
  positivity

lemma indicator_subset_prod {α : Type*} [DecidableEq α] (A s : Finset α) :
    (if s ⊆ A then (1 : ℝ) else 0) = ∏ i ∈ s, (if i ∈ A then 1 else 0) := by
  by_cases h : s ⊆ A
  · rw [ite_eq_left h]
    exact (Finset.prod_eq_one (fun i hi => ite_eq_left (h hi))).symm
  · rw [ite_eq_right h]
    obtain ⟨i, hi, hiA⟩ := Finset.not_subset.mp h
    exact (Finset.prod_eq_zero hi (ite_eq_right hiA)).symm

lemma inclusionMoment_const {α Ω : Type*} [DecidableEq α] [Fintype Ω] [Nonempty Ω]
    (A s : Finset α) : inclusionMoment (fun _ : Ω => A) s =
      if s ⊆ A then 1 else 0 := by
  classical
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases h : s ⊆ A <;> simp [inclusionMoment, finiteMean, h, hn]

lemma cylinder_const {α Ω : Type*} [Fintype Ω] [Nonempty Ω] (A : Finset α) :
    CylinderBound (inclusionMoment (fun _ : Ω => A))
      (fun i => inclusionMoment (fun _ : Ω => A) {i}) := by
  classical
  intro s
  simp only [inclusionMoment_const, Finset.singleton_subset_iff]
  exact (indicator_subset_prod A s).le

noncomputable def fairSetSwap {α Ω : Type*} [DecidableEq α]
    (F : Ω → Finset α) (a b : α) : Ω × Bool → Finset α :=
  fun ω => if ω.2 then (F ω.1).image (Equiv.swap a b) else F ω.1

lemma subset_swap_image_iff {α : Type*} [DecidableEq α]
    (A s : Finset α) (a b : α) :
    s ⊆ A.image (Equiv.swap a b) ↔ s.image (Equiv.swap a b) ⊆ A := by
  constructor
  · intro h
    have h' := Finset.image_subset_image h (f := Equiv.swap a b)
    simpa only [Finset.image_image, Function.comp_def, Equiv.swap_apply_self, Finset.image_id'] using h'
  · intro h
    have h' := Finset.image_subset_image h (f := Equiv.swap a b)
    simpa only [Finset.image_image, Function.comp_def, Equiv.swap_apply_self, Finset.image_id'] using h'

lemma inclusionMoment_fairSetSwap {α Ω : Type*} [DecidableEq α] [Fintype Ω]
    (F : Ω → Finset α) (a b : α) (s : Finset α) :
    inclusionMoment (fairSetSwap F a b) s =
      (inclusionMoment F s + inclusionMoment F (s.image (Equiv.swap a b))) / 2 := by
  classical
  simp only [inclusionMoment, finiteMean, Fintype.sum_prod_type, Fintype.sum_bool,
    fairSetSwap, Bool.false_eq_true, ↓reduceIte, Fintype.card_prod, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_ofNat, subset_swap_image_iff, Finset.sum_add_distrib]
  rw [div_mul_eq_div_div, add_div]
  ring_nf

lemma cylinder_fairSetSwap {α Ω : Type*} [DecidableEq α] [Fintype Ω]
    (F : Ω → Finset α) (a b : α)
    (h : CylinderBound (inclusionMoment F) (fun i => inclusionMoment F {i})) :
    CylinderBound (inclusionMoment (fairSetSwap F a b))
      (fun i => inclusionMoment (fairSetSwap F a b) {i}) := by
  classical
  have h' := h.fair_swap (fun i => inclusionMoment_nonneg F {i}) a b
  intro s
  simpa only [inclusionMoment_fairSetSwap, Finset.image_singleton] using h' s

def SwitchSamples : ℕ → Type
  | 0 => Unit
  | n + 1 => SwitchSamples n × Bool

instance (n : ℕ) : Fintype (SwitchSamples n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (SwitchSamples n × Bool))

instance (n : ℕ) : Nonempty (SwitchSamples n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih => exact inferInstanceAs (Nonempty (SwitchSamples n × Bool))

noncomputable def switchedSet {α : Type*} [DecidableEq α] (A : Finset α) :
    (L : List (α × α)) → SwitchSamples L.length → Finset α
  | [], _ => A
  | (a,b) :: L, ω => fairSetSwap (switchedSet A L) a b ω

lemma switchedSet_cylinder {α : Type*} [DecidableEq α] (A : Finset α)
    (L : List (α × α)) :
    CylinderBound (inclusionMoment (switchedSet A L))
      (fun i => inclusionMoment (switchedSet A L) {i}) := by
  induction L with
  | nil => exact cylinder_const A
  | cons e L ih => exact cylinder_fairSetSwap (switchedSet A L) e.1 e.2 ih

inductive QueryTree (ι : Type*)
  | reject : QueryTree ι
  | accept : QueryTree ι
  | branch (i : ι) (zero one : QueryTree ι) : QueryTree ι
  | force (i : ι) (b : Bool) (next : QueryTree ι) : QueryTree ι

namespace QueryTree

variable {ι : Type*} [DecidableEq ι]

def queries : QueryTree ι → Finset ι
  | reject => ∅
  | accept => ∅
  | branch i zero one => insert i (queries zero ∪ queries one)
  | force i _ next => insert i (queries next)

def Fresh : QueryTree ι → Prop
  | reject => True
  | accept => True
  | branch i zero one => i ∉ queries zero ∧ i ∉ queries one ∧ Fresh zero ∧ Fresh one
  | force i _ next => i ∉ queries next ∧ Fresh next

def weighted : QueryTree ι → (ι → Bool) → ℝ
  | reject, _ => 0
  | accept, _ => 1
  | branch i zero one, ω => if ω i then weighted one ω else weighted zero ω
  | force i b next, ω => if ω i = b then 2 * weighted next ω else 0

omit [DecidableEq ι] in
lemma weighted_nonneg (T : QueryTree ι) (ω : ι → Bool) : 0 ≤ T.weighted ω := by
  induction T with
  | reject => exact le_rfl
  | accept => exact zero_le_one
  | branch i zero one ih₀ ih₁ => simpa only [weighted] using ite_nonneg ih₁ ih₀
  | force i b next ih => simpa only [weighted] using ite_nonneg (mul_nonneg (by norm_num) ih) le_rfl

lemma weighted_congr (T : QueryTree ι) {ω η : ι → Bool}
    (h : ∀ i ∈ T.queries, ω i = η i) : T.weighted ω = T.weighted η := by
  induction T with
  | reject => rfl
  | accept => rfl
  | branch i zero one ih₀ ih₁ =>
    have hi := h i (Finset.mem_insert_self _ _)
    simp only [weighted, hi]
    rw [ih₀ (fun j hj => h j (Finset.mem_insert_of_mem (Finset.mem_union_left _ hj))),
      ih₁ (fun j hj => h j (Finset.mem_insert_of_mem (Finset.mem_union_right _ hj)))]
  | force i b next ih =>
    have hi := h i (Finset.mem_insert_self _ _)
    simp only [weighted, hi]
    rw [ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

def flipCoin (i : ι) : Equiv.Perm (ι → Bool) :=
  (show Function.Involutive (fun ω : ι → Bool => Function.update ω i (!(ω i))) from by
    intro ω
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]).toPerm

lemma flipCoin_apply_eq (i : ι) (ω : ι → Bool) : flipCoin i ω i = !(ω i) := by
  change Function.update ω i (!(ω i)) i = _
  exact Function.update_self _ _ _

lemma flipCoin_apply_ne (i j : ι) (h : j ≠ i) (ω : ι → Bool) :
    flipCoin i ω j = ω j := by
  change Function.update ω i (!(ω i)) j = _
  exact Function.update_of_ne h _ _

lemma weighted_flip_of_not_mem (T : QueryTree ι) (i : ι) (hi : i ∉ T.queries)
    (ω : ι → Bool) : T.weighted (flipCoin i ω) = T.weighted ω := by
  apply weighted_congr
  intro j hj
  exact flipCoin_apply_ne i j (fun h => hi (h ▸ hj)) ω

lemma mean_indicator_bit [Fintype ι] (f : (ι → Bool) → ℝ) (i : ι) (b : Bool)
    (hf : ∀ ω, f (flipCoin i ω) = f ω) :
    finiteMean (fun ω => if ω i = b then f ω else 0) = finiteMean f / 2 := by
  let g := fun ω : ι → Bool => if ω i = b then f ω else 0
  have hp (ω : ι → Bool) : g ω + g (flipCoin i ω) = f ω := by
    dsimp [g]
    rw [flipCoin_apply_eq, hf]
    cases hω : ω i <;> cases b <;> simp
  have hs := Equiv.sum_comp (flipCoin i) g
  have hadd : (∑ ω, g ω) + (∑ ω, g (flipCoin i ω)) = ∑ ω, f ω := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => hp ω)
  unfold finiteMean
  change (∑ ω, g ω) / _ = _
  rw [hs] at hadd
  have hh : (∑ ω, g ω) = (∑ ω, f ω) / 2 := by linarith
  rw [hh]
  ring

lemma mean_weighted_le_one [Fintype ι] (T : QueryTree ι) (hT : T.Fresh) :
    finiteMean T.weighted ≤ 1 := by
  induction T with
  | reject => simp [weighted, finiteMean]
  | accept => simp [weighted, finiteMean]
  | branch i zero one ih₀ ih₁ =>
    obtain ⟨hz, ho, hfz, hfo⟩ := hT
    have h₀ := mean_indicator_bit zero.weighted i false (zero.weighted_flip_of_not_mem i hz)
    have h₁ := mean_indicator_bit one.weighted i true (one.weighted_flip_of_not_mem i ho)
    have he : finiteMean (branch i zero one).weighted =
        finiteMean (fun ω => if ω i = false then zero.weighted ω else 0) +
        finiteMean (fun ω => if ω i = true then one.weighted ω else 0) := by
      unfold finiteMean
      rw [← add_div, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      cases hω : ω i <;> simp [weighted, hω]
    rw [he, h₀, h₁]
    linarith [ih₀ hfz, ih₁ hfo]
  | force i b next ih =>
    obtain ⟨hi, hn⟩ := hT
    have hm := mean_indicator_bit next.weighted i b (next.weighted_flip_of_not_mem i hi)
    have he : finiteMean (force i b next).weighted =
        2 * finiteMean (fun ω => if ω i = b then next.weighted ω else 0) := by
      unfold finiteMean
      rw [← mul_div_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : ω i = b <;> simp [weighted, h]
    rw [he, hm]
    linarith [ih hn]

def succeeds : QueryTree ι → (ι → Bool) → Bool
  | reject, _ => false
  | accept, _ => true
  | branch i zero one, ω => if ω i then succeeds one ω else succeeds zero ω
  | force i b next, ω => if ω i = b then succeeds next ω else false

def charge : QueryTree ι → (ι → Bool) → ℕ
  | reject, _ => 0
  | accept, _ => 0
  | branch i zero one, ω => if ω i then charge one ω else charge zero ω
  | force i b next, ω => if ω i = b then charge next ω + 1 else 0

omit [DecidableEq ι] in
lemma weighted_eq (T : QueryTree ι) (ω : ι → Bool) :
    T.weighted ω = if T.succeeds ω then (2 : ℝ) ^ T.charge ω else 0 := by
  induction T with
  | reject => rfl
  | accept => norm_num [weighted, succeeds, charge]
  | branch i zero one ih₀ ih₁ =>
    cases h : ω i <;> simp [weighted, succeeds, charge, h, ih₀, ih₁]
  | force i b next ih =>
    by_cases h : ω i = b
    · simp only [weighted, succeeds, charge, h, ↓reduceIte, ih]
      cases hs : next.succeeds ω <;> simp [pow_succ, mul_comm]
    · simp [weighted, succeeds, h]

lemma success_probability_le [Fintype ι] (T : QueryTree ι) (hT : T.Fresh)
    (K : ℕ) (hK : ∀ ω, T.succeeds ω = true → K ≤ T.charge ω) :
    finiteMean (fun ω => if T.succeeds ω then (1 : ℝ) else 0) ≤ 1 / (2 : ℝ) ^ K := by
  have hw (ω : ι → Bool) :
      (2 : ℝ) ^ K * (if T.succeeds ω then (1 : ℝ) else 0) ≤ T.weighted ω := by
    rw [weighted_eq]
    cases hs : T.succeeds ω
    · simp
    · simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (hK ω hs)
  have hn : 0 ≤ (Fintype.card (ι → Bool) : ℝ) := Nat.cast_nonneg _
  have hm := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hw ω)) hn
  rw [← Finset.mul_sum, mul_div_assoc] at hm
  change (2 : ℝ) ^ K * finiteMean (fun ω => if T.succeeds ω then 1 else 0) ≤
    finiteMean T.weighted at hm
  exact (le_div_iff₀ (pow_pos (by norm_num) K)).mpr (by
    rw [mul_comm]
    exact hm.trans (mean_weighted_le_one T hT))

end QueryTree

def encodeButterfly : (d : ℕ) → Butterfly d → SwitchIndex d → Bool
  | 0, _, i => nomatch i
  | _d + 1, b, Sum.inl y => b.1 y
  | d + 1, b, Sum.inr (ε,i) => encodeButterfly d (b.2 ε) i

lemma decode_encodeButterfly (d : ℕ) (b : Butterfly d) :
    decodeButterfly d (encodeButterfly d b) = b := by
  induction d with
  | zero => exact Unit.ext _ _
  | succ d ih =>
    apply Prod.ext
    · rfl
    · funext ε
      exact ih (b.2 ε)

lemma encode_decodeButterfly (d : ℕ) (ω : SwitchIndex d → Bool) :
    encodeButterfly d (decodeButterfly d ω) = ω := by
  induction d with
  | zero => funext i; exact Empty.elim i
  | succ d ih =>
    funext i
    cases i with
    | inl y => rfl
    | inr z => exact congrFun (ih (fun i => ω (Sum.inr (z.1,i)))) z.2

def butterflyCoinEquiv (d : ℕ) : (SwitchIndex d → Bool) ≃ Butterfly d where
  toFun := decodeButterfly d
  invFun := encodeButterfly d
  left_inv := encode_decodeButterfly d
  right_inv := decode_encodeButterfly d

noncomputable def routeDomain : (d : ℕ) → Card d → Card d → Finset (SwitchIndex d)
  | 0, _, _ => ∅
  | d + 1, x, y => by
      classical
      exact insert (Sum.inl (Fin.tail y))
        ((routeDomain d (Fin.tail x) (Fin.tail y)).image (fun i => Sum.inr (x 0,i)))

def routeValue : (d : ℕ) → Card d → Card d → SwitchIndex d → Bool
  | 0, _, _, i => nomatch i
  | _d + 1, x, y, Sum.inl _ => Bool.xor (x 0) (y 0)
  | d + 1, x, y, Sum.inr (_,i) => routeValue d (Fin.tail x) (Fin.tail y) i

end Thorp

end ThorpNine.Adaptive

end OAI

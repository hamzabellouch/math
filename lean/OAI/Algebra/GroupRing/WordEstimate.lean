import Mathlib

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors
namespace WordEstimate

open scoped BigOperators

abbrev Letter := (Fin 3 ⊕ Fin 8255) × Bool

def inverse (t : Letter) : Letter := (t.1, !t.2)

def IsExtra (t : Letter) : Prop := ∃ i : Fin 3, t = (Sum.inl i, true)

instance (t : Letter) : Decidable (IsExtra t) := inferInstanceAs (Decidable (∃ _, _))

@[simp] theorem isExtra_inl (i : Fin 3) (b : Bool) :
    IsExtra (Sum.inl i, b) ↔ b = true := by simp [IsExtra, Prod.mk.injEq]

@[simp] theorem not_isExtra_inr (i : Fin 8255) (b : Bool) :
    ¬IsExtra (Sum.inr i, b) := by simp [IsExtra]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  simp [inverse]

theorem inverse_ne (t : Letter) : inverse t ≠ t := by
  rcases t with ⟨i, b⟩
  cases b <;> simp [inverse]

theorem extra_inverse_not_extra (t : Letter) (h : IsExtra t) : ¬IsExtra (inverse t) := by
  obtain ⟨i, rfl⟩ := h
  simp [inverse]

/-- The exact marginal letter frequency `p=129/16513`. -/
def p : ℝ := 129 / 16513

/-- Conditional turn weights on side B before setting cancelling turns to zero. -/
def baseWeight (t u : Letter) : ℝ :=
  if IsExtra (inverse t) then (if IsExtra u then 1 else p)
  else (if IsExtra u then p else 1 / 129)

/-- Source `w(t,u)`, including zero on cancelling turns. -/
def weight (t u : Letter) : ℝ := if u = inverse t then 0 else baseWeight t u

/-- The positive test vector in the manuscript's matrix argument. -/
def f (t : Letter) : ℝ := if IsExtra (inverse t) then 5 else 1

theorem one_le_f (t : Letter) : 1 ≤ f t := by
  unfold f
  split_ifs <;> norm_num

theorem f_extra (t : Letter) (h : IsExtra t) : f t = 1 := by
  simp [f, extra_inverse_not_extra t h]

theorem sum_f : (∑ t : Letter, f t) = 16528 := by
  simp [Letter, Fintype.sum_prod_type, Fintype.sum_sum_type,
    f, inverse]
  norm_num

/-- The two row types have the exact untruncated mass given by the source. -/
theorem base_row_mass (t : Letter) :
    (∑ u : Letter, baseWeight t u ^ 2 * f u) =
      if IsExtra (inverse t) then 3 + 16525 * p ^ 2
      else 3 * p ^ 2 + 16525 / 129 ^ 2 := by
  unfold baseWeight
  split_ifs with h
  · simp [Letter, Fintype.sum_prod_type, Fintype.sum_sum_type,
      f, inverse]
    ring
  · simp [Letter, Fintype.sum_prod_type, Fintype.sum_sum_type,
      f, inverse]
    ring

/-- Removing the cancelling turn removes precisely its diagonal summand. -/
theorem row_mass (t : Letter) :
    (∑ u : Letter, weight t u ^ 2 * f u) =
      (∑ u : Letter, baseWeight t u ^ 2 * f u) -
        baseWeight t (inverse t) ^ 2 * f (inverse t) := by
  classical
  have h (u : Letter) : weight t u ^ 2 * f u =
      baseWeight t u ^ 2 * f u -
        if u = inverse t then baseWeight t u ^ 2 * f u else 0 := by
    by_cases hu : u = inverse t <;> simp [weight, hu]
  simp_rw [h, Finset.sum_sub_distrib]
  simp

/-- `Mf ≤ (149/150)f`, with the exact alphabet, weights and constants. -/
theorem matrix_contraction (t : Letter) :
    (∑ u : Letter, weight t u ^ 2 * f u) ≤ (149 / 150 : ℝ) * f t := by
  rw [row_mass, base_row_mass]
  by_cases h : IsExtra (inverse t)
  · have hfi : f (inverse t) = 1 := f_extra _ h
    have hft : f t = 5 := by simp [f, h]
    simp only [h, ite_true, baseWeight, hfi, hft]
    norm_num [p]
  · have hf := one_le_f (inverse t)
    have hft : f t = 1 := by simp [f, h]
    simp only [h, ite_false, baseWeight, hft]
    norm_num [p]
    nlinarith

/-- Product of the turn weights from a starting letter through a tail. -/
def continuation : (n : ℕ) → Letter → (Fin n → Letter) → ℝ
  | 0, _, _ => 1
  | n + 1, t, W => weight t (W 0) * continuation n (W 0) (Fin.tail W)

/-- Source `P(W)`, with empty products equal to one. -/
def wordWeight : (h : ℕ) → (Fin h → Letter) → ℝ
  | 0, _ => 1
  | h + 1, W => continuation h (W 0) (Fin.tail W)

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Letter) → ℝ) :
    (∑ W, F W) = ∑ t, ∑ W, F (Fin.cons t W) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Letter)).sum_comp F]
  rw [Fintype.sum_prod_type]
  rfl

/-- Iterating the exact matrix contraction controls all tails simultaneously. -/
theorem continuation_mass (n : ℕ) (t : Letter) :
    (∑ W : Fin n → Letter, continuation n t W ^ 2) ≤
      (149 / 150 : ℝ) ^ n * f t := by
  induction n generalizing t with
  | zero => simpa [continuation] using one_le_f t
  | succ n ih =>
    rw [sum_cons]
    simp only [continuation, Fin.cons_zero, Fin.tail_cons, mul_pow]
    simp_rw [← Finset.mul_sum]
    calc
      ∑ u, weight t u ^ 2 * ∑ W : Fin n → Letter, continuation n u W ^ 2
          ≤ ∑ u, weight t u ^ 2 * ((149 / 150 : ℝ) ^ n * f u) := by
            apply Finset.sum_le_sum
            intro u _
            exact mul_le_mul_of_nonneg_left (ih u) (sq_nonneg _)
      _ = (149 / 150 : ℝ) ^ n * ∑ u, weight t u ^ 2 * f u := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            ring
      _ ≤ (149 / 150 : ℝ) ^ n * ((149 / 150 : ℝ) * f t) := by
            apply mul_le_mul_of_nonneg_left (matrix_contraction t)
            positivity
      _ = (149 / 150 : ℝ) ^ (n + 1) * f t := by ring

/-- The matrix form of the squared-word estimate, before exponent conversion. -/
theorem squared_word_geometric_bound (h : ℕ) :
    (∑ W : Fin (h + 1) → Letter, wordWeight (h + 1) W ^ 2) ≤
      16528 * (149 / 150 : ℝ) ^ h := by
  rw [sum_cons]
  simp only [wordWeight, Fin.cons_zero, Fin.tail_cons]
  calc
    ∑ t, ∑ W : Fin h → Letter, continuation h t W ^ 2
        ≤ ∑ t, (149 / 150 : ℝ) ^ h * f t := by
          exact Finset.sum_le_sum fun t _ ↦ continuation_mass h t
    _ = 16528 * (149 / 150 : ℝ) ^ h := by
          rw [← Finset.mul_sum, sum_f]
          ring

theorem continuation_eq_product (n : ℕ) (t : Letter) (W : Fin n → Letter) :
    continuation n t W =
      ∏ i : Fin n, weight ((Fin.cons t W : Fin (n + 1) → Letter) i.castSucc)
        ((Fin.cons t W : Fin (n + 1) → Letter) i.succ) := by
  induction n generalizing t with
  | zero => simp [continuation]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simp only [continuation, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
      ih]
    simp only [Fin.cons_self_tail, Fin.castSucc_succ, Fin.cons_succ, Fin.tail]

theorem wordWeight_eq_product (h : ℕ) (W : Fin (h + 1) → Letter) :
    wordWeight (h + 1) W = ∏ i : Fin h, weight (W i.castSucc) (W i.succ) := by
  rw [wordWeight, continuation_eq_product]
  simp only [Fin.cons_self_tail]

theorem constant_le_exp : (16528 : ℝ) ≤ Real.exp 10 := by
  calc
    (16528 : ℝ) ≤ (27 / 10 : ℝ) ^ 10 := by norm_num
    _ ≤ Real.exp 1 ^ 10 := by
      gcongr
      exact le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
    _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num

theorem ratio_le_exp : (149 / 150 : ℝ) ≤ Real.exp (-1 / 150) := by
  have h := Real.add_one_le_exp (-1 / 150)
  linarith

/-- The manuscript's exact numerical cutoff, without asymptotic weakening. -/
theorem geometric_exponential_bound (n : ℕ) (hn : 3001 ≤ n) :
    16528 * (149 / 150 : ℝ) ^ n ≤ Real.exp (-((n : ℝ) + 1) / 300) := by
  calc
    16528 * (149 / 150 : ℝ) ^ n
        ≤ Real.exp 10 * Real.exp (-1 / 150) ^ n := by
            apply mul_le_mul constant_le_exp
            · gcongr; exact ratio_le_exp
            · positivity
            · positivity
    _ = Real.exp (10 + (n : ℝ) * (-1 / 150)) := by
          rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp (-((n : ℝ) + 1) / 300) := by
          apply Real.exp_le_exp.mpr
          have hn' : (3001 : ℝ) ≤ n := by exact_mod_cast hn
          linarith

/-- Source lemma `lem:squared-words`, with its exhibited delta=1/600. -/
theorem squared_word_estimate (h : ℕ) (hh : 3002 ≤ h) :
    (∑ W : Fin h → Letter, wordWeight h W ^ 2) ≤
      Real.exp (-2 * (1 / 600 : ℝ) * h) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  have hn : 3001 ≤ n := by omega
  have hbound := le_trans (squared_word_geometric_bound n)
    (geometric_exponential_bound n hn)
  apply hbound.trans_eq
  congr 1
  simp only [Nat.cast_succ]
  ring

/-! Binning the weights: entropy.tex, equation (entropy-bins). -/

theorem weight_nonneg (t u : Letter) : 0 ≤ weight t u := by
  unfold weight baseWeight p
  split_ifs <;> norm_num

theorem weight_le_one (t u : Letter) : weight t u ≤ 1 := by
  unfold weight baseWeight p
  split_ifs <;> norm_num

theorem weight_pos_lower (t u : Letter) (h : 0 < weight t u) :
    (1 / 129 : ℝ) ≤ weight t u := by
  unfold weight baseWeight p at *
  split_ifs at * <;> norm_num at *

theorem continuation_nonneg (n : ℕ) (t : Letter) (W : Fin n → Letter) :
    0 ≤ continuation n t W := by
  rw [continuation_eq_product]
  exact Finset.prod_nonneg fun _ _ => weight_nonneg _ _

theorem wordWeight_nonneg (h : ℕ) (W : Fin h → Letter) : 0 ≤ wordWeight h W := by
  cases h with
  | zero => norm_num [wordWeight]
  | succ h => exact continuation_nonneg _ _ _

theorem wordWeight_upper (h : ℕ) (hh : 3002 ≤ h) (W : Fin h → Letter) :
    wordWeight h W ≤ Real.exp (-(1 / 600 : ℝ) * h) := by
  have hsingle : wordWeight h W ^ 2 ≤
      ∑ V : Fin h → Letter, wordWeight h V ^ 2 :=
    Finset.single_le_sum (fun V _ => sq_nonneg (wordWeight h V)) (Finset.mem_univ W)
  have he := hsingle.trans (squared_word_estimate h hh)
  have hexp : Real.exp (-2 * (1 / 600 : ℝ) * h) =
      Real.exp (-(1 / 600 : ℝ) * h) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at he
  nlinarith [Real.exp_pos (-(1 / 600 : ℝ) * h)]

/-- Exact logarithmic bins, excluding zero weights just as in the source. -/
def binWords (h : ℕ) (d : ℤ) : Finset (Fin h → Letter) :=
  Finset.univ.filter fun W => 0 < wordWeight h W ∧ ⌊-Real.log (wordWeight h W)⌋ = d

theorem bin_sq_lower {h : ℕ} {d : ℤ} {W : Fin h → Letter}
    (hW : W ∈ binWords h d) :
    Real.exp (-2 * (d : ℝ) - 2) ≤ wordWeight h W ^ 2 := by
  obtain ⟨hp, hd⟩ := (Finset.mem_filter.mp hW).2
  have hfloor := Int.lt_floor_add_one (-Real.log (wordWeight h W))
  rw [hd] at hfloor
  have hlog : -2 * (d : ℝ) - 2 ≤ 2 * Real.log (wordWeight h W) := by linarith
  have he := Real.exp_le_exp.mpr hlog
  have hpow : Real.exp (2 * Real.log (wordWeight h W)) = wordWeight h W ^ 2 := by
    rw [show (2 : ℝ) * Real.log (wordWeight h W) =
      (2 : ℕ) * Real.log (wordWeight h W) by norm_num, Real.exp_nat_mul, Real.exp_log hp]
  rwa [hpow] at he

/-- The exact finite bin-count bound before replacing h by its common scale. -/
theorem bin_card_bound (h : ℕ) (hh : 3002 ≤ h) (d : ℤ) :
    ((binWords h d).card : ℝ) ≤
      Real.exp (2 * (d : ℝ) + 2 - 2 * (1 / 600 : ℝ) * h) := by
  have hlo : ((binWords h d).card : ℝ) * Real.exp (-2 * (d : ℝ) - 2) ≤
      ∑ W ∈ binWords h d, wordWeight h W ^ 2 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun W hW => bin_sq_lower hW)
  have hsum : (∑ W ∈ binWords h d, wordWeight h W ^ 2) ≤
      ∑ W : Fin h → Letter, wordWeight h W ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun W _ _ => sq_nonneg _)
  have he := hlo.trans (hsum.trans (squared_word_estimate h hh))
  apply (le_div_iff₀ (Real.exp_pos _)).mpr at he
  apply he.trans_eq
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Both the lower bin cutoff and the counting bound at the scalar block
scale s. The displayed threshold absorbs the manuscript's rounding errors. -/
theorem bin_scale_bounds (h : ℕ) (hh : 3002 ≤ h) (s : ℝ)
    (hscale : s + 1200 ≤ 2 * h) (d : ℤ) (W : Fin h → Letter)
    (hW : W ∈ binWords h d) :
    (1 / 600 : ℝ) * s / 2 ≤ (d : ℝ) ∧
      ((binWords h d).card : ℝ) ≤ Real.exp (2 * d - (1 / 600 : ℝ) * s) := by
  obtain ⟨hp, hd⟩ := (Finset.mem_filter.mp hW).2
  have hw := wordWeight_upper h hh W
  have hlog : Real.log (wordWeight h W) ≤ -(1 / 600 : ℝ) * h := by
    have he := Real.log_le_log hp hw
    simpa only [Real.log_exp] using he
  have hfloor := Int.lt_floor_add_one (-Real.log (wordWeight h W))
  rw [hd] at hfloor
  constructor
  · linarith
  · apply (bin_card_bound h hh d).trans
    apply Real.exp_le_exp.mpr
    linarith

end WordEstimate
end TorsionFreeZeroDivisors

namespace TorsionFreeZeroDivisors.WordEstimate
open scoped BigOperators

/-- Every positive continuation has the uniform lower product bound from
its smallest allowed turn weight. -/
theorem continuation_lower (n : ℕ) (t : Letter) (W : Fin n → Letter)
    (hp : 0 < continuation n t W) :
    (1/129 : ℝ)^n ≤ continuation n t W := by
  induction n generalizing t with
  | zero => simp [continuation]
  | succ n ih =>
    dsimp [continuation] at hp ⊢
    have ht : 0 < weight t (W 0) := (mul_pos_iff.mp hp).elim (fun h => h.1)
      (fun h => False.elim (not_lt_of_ge (weight_nonneg _ _) h.1))
    have hu : 0 < continuation n (W 0) (fun i => W i.succ) :=
      (mul_pos_iff.mp hp).elim (fun h => h.2)
        (fun h => False.elim (not_lt_of_ge (weight_nonneg _ _) h.1))
    rw [pow_succ]
    exact mul_le_mul (ih _ _ hu) (weight_pos_lower _ _ ht) (by positivity)
      (continuation_nonneg _ _ _) |>.trans_eq (mul_comm _ _)

theorem wordWeight_lower (h : ℕ) (W : Fin h → Letter) (hp : 0 < wordWeight h W) :
    (1/129 : ℝ)^h ≤ wordWeight h W := by
  cases h with
  | zero => simp [wordWeight]
  | succ n =>
    have ht := continuation_lower n (W 0) (fun i => W i.succ) hp
    have hb : (1/129 : ℝ)^(n+1) ≤ (1/129 : ℝ)^n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) (by norm_num)
    exact hb.trans ht

/-- A coarse fixed upper bin constant; the manuscript leaves a₀ unspecified.
We choose a₀=256, avoiding any numerical transcendental oracle. -/
theorem bin_upper_bound (h : ℕ) (s : ℝ) (hscale : (h : ℝ) ≤ 2*s)
    (d : ℤ) (W : Fin h → Letter) (hW : W ∈ binWords h d) : (d : ℝ) ≤ 256*s := by
  obtain ⟨hp,hd⟩ := (Finset.mem_filter.mp hW).2
  have ht := wordWeight_lower h W hp
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (1/129 : ℝ)^h) ht
  rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hl
  have hlog : Real.log (129 : ℝ) ≤ 128 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<129)
    norm_num at hh ⊢
    exact hh
  have hb := Int.floor_le (-Real.log (wordWeight h W))
  rw [hd] at hb
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg h : (0:ℝ)≤h)
  nlinarith

/-- Both bin cutoffs and the squared-word count with literal δ=1/600 and
one universal upper constant. -/
theorem bin_full_bounds (h : ℕ) (hh : 3002 ≤ h) (s : ℝ)
    (hscale : s+1200 ≤ 2*h) (hscale' : (h : ℝ) ≤ 2*s)
    (d : ℤ) (W : Fin h → Letter) (hW : W ∈ binWords h d) :
    (1/600 : ℝ)*s/2 ≤ d ∧ (d : ℝ) ≤ 256*s ∧
      ((binWords h d).card : ℝ) ≤ Real.exp (2*d-(1/600 : ℝ)*s) := by
  obtain ⟨hl,hc⟩ := bin_scale_bounds h hh s hscale d W hW
  exact ⟨hl,bin_upper_bound h s hscale' d W hW,hc⟩

end TorsionFreeZeroDivisors.WordEstimate

/-! Source entropy.tex 300--458, with all local root counts evaluated rather
than assumed. A translation self-link saves the root; a component without one
uses its selected bin-minimizing root. Reflection self-links are ruled out by
`BlockConstraints.reflection_impossible` before this count is applied. -/

end

end OAI

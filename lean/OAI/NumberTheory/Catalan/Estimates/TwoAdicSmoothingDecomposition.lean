import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.LinearCombination
import OAI.NumberTheory.Catalan.Analysis.ContactSeries

namespace OAI


namespace InternalCatalan

theorem centralCoeff_two_adic_eq (l : ℕ) :
    padicValRat 2 (centralCoeff l) =
      (padicValNat 2 ((2 * l).choose l) : ℤ) - 2 * (l : ℤ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnum : (((2 * l).choose l : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.centralBinom_pos l))
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  have hfour : padicValRat 2 (4 : ℚ) = 2 := by
    rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, padicValRat.pow, htwo]
    norm_num
  unfold centralCoeff
  rw [padicValRat.div hnum (pow_ne_zero _ (by norm_num)),
    padicValRat.of_nat, padicValRat.pow, hfour]
  ring

theorem centralCoeff_two_adic_lower (l : ℕ) :
    -2 * (l : ℤ) ≤ padicValRat 2 (centralCoeff l) := by
  rw [centralCoeff_two_adic_eq]
  omega

theorem odd_nat_two_adic_eq_zero (l : ℕ) :
    padicValRat 2 ((2 * l + 1 : ℕ) : ℚ) = 0 := by
  have hn : ¬2 ∣ 2 * l + 1 := by omega
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hn]
  norm_num

theorem momentScalar_even_two_adic_eq (l : ℕ) :
    padicValRat 2 (momentScalar (2 * l)) =
      1 + 2 * (l : ℤ) - (padicValNat 2 ((2 * l).choose l) : ℤ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [momentScalar_even,
    padicValRat.div (by norm_num) (mul_ne_zero hodd (centralCoeff_ne_zero l)),
    padicValRat.mul hodd (centralCoeff_ne_zero l), htwo,
    odd_nat_two_adic_eq_zero, centralCoeff_two_adic_eq]
  ring

theorem centralBinom_two_adic_le_log (l : ℕ) :
    padicValNat 2 ((2 * l).choose l) ≤ Nat.log 2 (2 * l) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_choose (p := 2) (by omega : l ≤ 2 * l)
    (by omega : Nat.log 2 (2 * l) < Nat.log 2 (2 * l) + 1)]
  calc
    _ ≤ (Finset.Ico 1 (Nat.log 2 (2 * l) + 1)).card := Finset.card_filter_le _ _
    _ = Nat.log 2 (2 * l) := by simp

theorem momentScalar_even_two_adic_lower (l : ℕ) :
    1 + 2 * (l : ℤ) - (Nat.log 2 (2 * l) : ℤ) ≤
      padicValRat 2 (momentScalar (2 * l)) := by
  rw [momentScalar_even_two_adic_eq]
  have hb : (padicValNat 2 ((2 * l).choose l) : ℤ) ≤ (Nat.log 2 (2 * l) : ℤ) := by
    exact_mod_cast centralBinom_two_adic_le_log l
  omega

theorem momentScalar_even_div_two_adic_lower (l j : ℕ) :
    1 + 2 * (l : ℤ) - (Nat.log 2 (2 * l) : ℤ) - (Nat.log 2 (j + 1) : ℤ) ≤
      padicValRat 2 (momentScalar (2 * l) / ((j + 1 : ℕ) : ℚ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : momentScalar (2 * l) ≠ 0 := by
    rw [momentScalar_even]
    exact div_ne_zero (by norm_num)
      (mul_ne_zero (by positivity) (centralCoeff_ne_zero l))
  have hj : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [padicValRat.div hm hj, padicValRat.of_nat]
  have hmval := momentScalar_even_two_adic_lower l
  have hjval : (padicValNat 2 (j + 1) : ℤ) ≤ (Nat.log 2 (j + 1) : ℤ) := by
    exact_mod_cast padicValNat_le_nat_log (p := 2) (j + 1)
  omega





open Filter
open scoped Topology BigOperators

noncomputable def smoothingTerm (i j k : ℕ) : ℚ_[2] :=
  ((momentScalar (i + k) / ((j + k + 1 : ℕ) : ℚ) : ℚ) : ℚ_[2])

theorem smoothingTerm_norm_le_zpow (i j k : ℕ) :
    ‖smoothingTerm i j k‖ ≤
      (2 : ℝ) ^ ((Nat.log 2 (i + k) : ℤ) +
        (Nat.log 2 (j + k + 1) : ℤ) - ((i + k + 1 : ℕ) : ℤ)) := by
  by_cases hm : momentScalar (i + k) = 0
  · simp only [smoothingTerm, hm, zero_div, Rat.cast_zero, norm_zero]
    positivity
  have heven : (i + k) % 2 = 0 := by
    by_contra h
    exact hm (by simp [momentScalar, h])
  have hidx : 2 * ((i + k) / 2) = i + k := by omega
  have hv := momentScalar_even_div_two_adic_lower ((i + k) / 2) (j + k)
  rw [hidx] at hv
  have hq : momentScalar (i + k) / ((j + k + 1 : ℕ) : ℚ) ≠ 0 :=
    div_ne_zero hm (by positivity)
  have hq₂ : smoothingTerm i j k ≠ 0 := by
    unfold smoothingTerm
    exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hq₂]
  change (2 : ℝ) ^ (-Padic.valuation
    ((momentScalar (i + k) / ((j + k + 1 : ℕ) : ℚ) : ℚ) : ℚ_[2])) ≤ _
  rw [Padic.valuation_ratCast]
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  push_cast at hv ⊢
  have hidxZ : 2 * ((↑((i + k) / 2) : ℤ)) = (i : ℤ) + k := by
    exact_mod_cast hidx
  omega

theorem smoothingTerm_norm_le (i j k : ℕ) :
    ‖smoothingTerm i j k‖ ≤
      ((i + k + 1 : ℕ) : ℝ) * ((j + k + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k := by
  have ha : (2 : ℝ) ^ Nat.log 2 (i + k) ≤ ((i + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_add_one 2 (i + k)
  have hb : (2 : ℝ) ^ Nat.log 2 (j + k + 1) ≤ ((j + k + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_add_one 2 (j + k + 1)
  have hc : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (i + k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hd : 1 / (2 : ℝ) ^ (i + k + 1) ≤ (1 / 2 : ℝ) ^ k := by
    simpa only [one_div_pow] using
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ k) hc
  calc
    ‖smoothingTerm i j k‖ ≤
        (2 : ℝ) ^ ((Nat.log 2 (i + k) : ℤ) +
          (Nat.log 2 (j + k + 1) : ℤ) - ((i + k + 1 : ℕ) : ℤ)) :=
      smoothingTerm_norm_le_zpow i j k
    _ = ((2 : ℝ) ^ Nat.log 2 (i + k) * (2 : ℝ) ^ Nat.log 2 (j + k + 1)) /
        (2 : ℝ) ^ (i + k + 1) := by
      rw [zpow_sub₀ (by norm_num), zpow_add₀ (by norm_num)]
      simp only [zpow_natCast]
    _ ≤ (((i + k + 1 : ℕ) : ℝ) * ((j + k + 2 : ℕ) : ℝ)) /
        (2 : ℝ) ^ (i + k + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul ha hb (by positivity) (by positivity)) (by positivity)
    _ ≤ _ := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hd (by positivity)

private theorem smoothing_majorant_summable (i j : ℕ) :
    Summable (fun k : ℕ =>
      ((i + k + 1 : ℕ) : ℝ) * ((j + k + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) := by
  have h₀ := summable_geometric_two
  have h₁ := summable_pow_mul_geometric_of_norm_lt_one 1
    (r := (1 / 2 : ℝ)) (by norm_num)
  have h₂ := summable_pow_mul_geometric_of_norm_lt_one 2
    (r := (1 / 2 : ℝ)) (by norm_num)
  convert (h₂.add (h₁.mul_left ((i : ℝ) + j + 3))).add
    (h₀.mul_left (((i : ℝ) + 1) * ((j : ℝ) + 2))) using 1
  ext k
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_one]
  ring

theorem smoothingTerm_summable_norm (i j : ℕ) :
    Summable (fun k : ℕ => ‖smoothingTerm i j k‖) := by
  apply (smoothing_majorant_summable i j).of_norm_bounded
  intro k
  simpa only [norm_norm] using smoothingTerm_norm_le i j k

theorem smoothingTerm_summable (i j : ℕ) : Summable (smoothingTerm i j) :=
  (smoothingTerm_summable_norm i j).of_norm

noncomputable def smoothingMoment (i j : ℕ) : ℚ_[2] := ∑' k, smoothingTerm i j k

theorem smoothingMoment_hasSum (i j : ℕ) :
    HasSum (smoothingTerm i j) (smoothingMoment i j) :=
  (smoothingTerm_summable i j).hasSum

theorem smoothingTerm_tendsto_zero (i j : ℕ) :
    Tendsto (smoothingTerm i j) atTop (𝓝 0) :=
  (smoothingTerm_summable i j).tendsto_atTop_zero

theorem smoothingMoment_step (i j : ℕ) :
    smoothingMoment i j - smoothingMoment (i + 1) (j + 1) =
      ((momentScalar i / ((j + 1 : ℕ) : ℚ) : ℚ) : ℚ_[2]) := by
  have hshift : (fun k : ℕ => smoothingTerm i j (k + 1)) =
      smoothingTerm (i + 1) (j + 1) := by
    funext k
    simp only [smoothingTerm, Nat.add_left_comm, Nat.add_comm]
  have hs := (smoothingTerm_summable i j).tsum_eq_zero_add
  rw [hshift] at hs
  change smoothingMoment i j = smoothingTerm i j 0 + smoothingMoment (i + 1) (j + 1) at hs
  rw [hs, add_sub_cancel_right]
  simp [smoothingTerm]

end InternalCatalan



namespace InternalCatalan

open Filter
open scoped Topology BigOperators

private theorem smoothing_square_le_pow (k : ℕ) : (k + 1) ^ 2 ≤ 2 ^ (k + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases h₀ : k = 0
    · subst k
      norm_num
    by_cases h₁ : k = 1
    · subst k
      norm_num
    have hk : 2 ≤ k := by omega
    calc
      (k + 1 + 1) ^ 2 ≤ 2 * (k + 1) ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ (k + 2) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1 + 2) := by
        simp only [pow_add, pow_one, pow_two]
        ring

theorem smoothingTerm_norm_le_uniform (H i j k : ℕ) (hi : i < H) (hj : j < H) :
    ‖smoothingTerm i j k‖ ≤ 2 * (H : ℝ) ^ 2 / (2 : ℝ) ^ i := by
  have hH : 0 < H := by omega
  have ha : (2 : ℝ) ^ Nat.log 2 (i + k) ≤ ((H + k : ℕ) : ℝ) := by
    exact_mod_cast (le_trans (Nat.pow_log_le_add_one 2 (i + k))
      (by omega : i + k + 1 ≤ H + k))
  have hb : (2 : ℝ) ^ Nat.log 2 (j + k + 1) ≤ ((H + k : ℕ) : ℝ) := by
    exact_mod_cast (le_trans (Nat.pow_log_le_self 2 (by omega : j + k + 1 ≠ 0))
      (by omega : j + k + 1 ≤ H + k))
  have hc : ((H + k : ℕ) : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 * (2 : ℝ) ^ (k + 2) := by
    have hlin : H + k ≤ H * (k + 1) := by nlinarith
    have hpoly : (H + k) ^ 2 ≤ H ^ 2 * (k + 1) ^ 2 := by
      simpa only [mul_pow] using Nat.pow_le_pow_left hlin 2
    have hbound := Nat.mul_le_mul_left (H ^ 2) (smoothing_square_le_pow k)
    exact_mod_cast le_trans hpoly hbound
  calc
    ‖smoothingTerm i j k‖ ≤
        (2 : ℝ) ^ ((Nat.log 2 (i + k) : ℤ) +
          (Nat.log 2 (j + k + 1) : ℤ) - ((i + k + 1 : ℕ) : ℤ)) :=
      smoothingTerm_norm_le_zpow i j k
    _ = ((2 : ℝ) ^ Nat.log 2 (i + k) * (2 : ℝ) ^ Nat.log 2 (j + k + 1)) /
        (2 : ℝ) ^ (i + k + 1) := by
      rw [zpow_sub₀ (by norm_num), zpow_add₀ (by norm_num)]
      simp only [zpow_natCast]
    _ ≤ ((H + k : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ (i + k + 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [pow_two] using mul_le_mul ha hb (by positivity) (by positivity)
    _ ≤ ((H : ℝ) ^ 2 * (2 : ℝ) ^ (k + 2)) / (2 : ℝ) ^ (i + k + 1) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = 2 * (H : ℝ) ^ 2 / (2 : ℝ) ^ i := by
      rw [show i + k + 1 = i + (k + 1) by omega]
      simp only [pow_add, pow_one, pow_two]
      field_simp

theorem smoothingMoment_norm_le_uniform (H i j : ℕ) (hi : i < H) (hj : j < H) :
    ‖smoothingMoment i j‖ ≤ 2 * (H : ℝ) ^ 2 / (2 : ℝ) ^ i := by
  have hpartial : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, smoothingTerm i j k‖ ≤
      2 * (H : ℝ) ^ 2 / (2 : ℝ) ^ i := by
    intro n
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, norm_zero]; positivity
    | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (Padic.nonarchimedean _ _).trans
        (max_le ih (smoothingTerm_norm_le_uniform H i j n hi hj))
  exact le_of_tendsto_of_tendsto'
    ((smoothingMoment_hasSum i j).tendsto_sum_nat.norm) tendsto_const_nhds hpartial

end InternalCatalan



noncomputable section

open Filter
open scoped BigOperators Topology

namespace InternalCatalan

private theorem smoothingScalar_step (n : ℕ) :
    ((n + 3 : ℕ) : ℚ) * momentScalar (n + 2) =
      ((n + 2 : ℕ) : ℚ) * momentScalar n := by
  rcases Nat.even_or_odd' n with ⟨l, rfl | rfl⟩
  · rw [show 2 * l + 2 = 2 * (l + 1) by omega,
      momentScalar_even, momentScalar_even]
    have hc := centralCoeff_step l
    have hc' := congrArg (fun x : ℚ => ((2 * l + 3 : ℕ) : ℚ) * x) hc
    have hc0 := centralCoeff_ne_zero l
    have hc1 := centralCoeff_ne_zero (l + 1)
    have hden0 : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hden1 : ((2 * (l + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast at hc' ⊢
    field_simp
    nlinarith only [hc']
  · rw [show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega,
      momentScalar_odd, momentScalar_odd]
    ring

theorem momentScalar_padic_tendsto_zero :
    Tendsto (fun n : ℕ => (momentScalar n : ℚ_[2])) atTop (𝓝 0) := by
  have hnorm (n : ℕ) : ‖(momentScalar n : ℚ_[2])‖ ≤ ‖smoothingTerm 0 0 n‖ := by
    have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have he : (momentScalar n : ℚ_[2]) =
        ((n + 1 : ℕ) : ℚ_[2]) * smoothingTerm 0 0 n := by
      simp only [smoothingTerm, Nat.zero_add]
      exact_mod_cast (show momentScalar n =
        ((n + 1 : ℕ) : ℚ) * (momentScalar n / ((n + 1 : ℕ) : ℚ)) by
          field_simp)
    have hb : ‖((n + 1 : ℕ) : ℚ_[2])‖ ≤ 1 := by
      simpa only [Int.cast_natCast] using
        (Padic.norm_int_le_one (p := 2) ((n + 1 : ℕ) : ℤ))
    rw [he, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hb
  apply squeeze_zero_norm hnorm
  simpa only [norm_zero] using (smoothingTerm_tendsto_zero 0 0).norm

private theorem smoothing_sum_range_sub_add_two (f : ℕ → ℚ_[2]) (n : ℕ) :
    (∑ u ∈ Finset.range n, (f u - f (u + 2))) =
      f 0 + f 1 - f n - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private theorem smoothing_hasSum_sub_add_two_value (f : ℕ → ℚ_[2])
    (hf : Tendsto f atTop (𝓝 0)) {a : ℚ_[2]}
    (ha : HasSum (fun u => f u - f (u + 2)) a) : a = f 0 + f 1 := by
  have ht : Tendsto (fun n => f 0 + f 1 - f n - f (n + 1))
      atTop (𝓝 (f 0 + f 1)) := by
    simpa using
      ((tendsto_const_nhds.sub hf).sub (hf.comp (tendsto_add_atTop_nat 1)))
  have hs := ha.tendsto_sum_nat
  simp only [smoothing_sum_range_sub_add_two] at hs
  exact tendsto_nhds_unique hs ht

theorem smoothingMoment_first_boundary_step (d : ℕ) :
    ((d + 2 : ℕ) : ℚ_[2]) * smoothingMoment (d + 2) 0 =
      ((d + 1 : ℕ) : ℚ_[2]) * smoothingMoment d 0 +
        (momentScalar d : ℚ_[2]) + (momentScalar (d + 1) : ℚ_[2]) := by
  have hs := ((smoothingMoment_hasSum (d + 2) 0).mul_left
      ((d + 2 : ℕ) : ℚ_[2])).sub
    ((smoothingMoment_hasSum d 0).mul_left ((d + 1 : ℕ) : ℚ_[2]))
  have hs' : HasSum
      (fun u => (momentScalar (d + u) : ℚ_[2]) -
        (momentScalar (d + u + 2) : ℚ_[2]))
      (((d + 2 : ℕ) : ℚ_[2]) * smoothingMoment (d + 2) 0 -
        ((d + 1 : ℕ) : ℚ_[2]) * smoothingMoment d 0) := by
    convert hs using 1
    ext u
    have hrec := smoothingScalar_step (d + u)
    have hq : momentScalar (d + u) - momentScalar (d + u + 2) =
        ((d + 2 : ℕ) : ℚ) *
          (momentScalar (d + 2 + u) / ((u + 1 : ℕ) : ℚ)) -
        ((d + 1 : ℕ) : ℚ) *
          (momentScalar (d + u) / ((u + 1 : ℕ) : ℚ)) := by
      rw [show d + 2 + u = d + u + 2 by omega]
      have hu : (u : ℚ) + 1 ≠ 0 := by positivity
      push_cast at hrec ⊢
      field_simp [hu]
      nlinarith only [hrec]
    simpa only [smoothingTerm, Nat.zero_add, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℚ_[2])) hq
  have hlim : Tendsto (fun u => (momentScalar (d + u) : ℚ_[2])) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm d] using
      momentScalar_padic_tendsto_zero.comp (tendsto_add_atTop_nat d)
  have hv := smoothing_hasSum_sub_add_two_value _ hlim hs'
  simp only [Nat.add_zero] at hv
  linear_combination hv

theorem smoothingMoment_one_zero : smoothingMoment 1 0 = 2 := by
  have hs := (hasSum_nat_add_iff' 1).mpr (smoothingMoment_hasSum 1 0)
  have hs' : HasSum
      (fun u => (momentScalar u : ℚ_[2]) - (momentScalar (u + 2) : ℚ_[2]))
      (smoothingMoment 1 0) := by
    convert hs using 1
    · ext u
      have hrec := smoothingScalar_step u
      have hq : momentScalar u - momentScalar (u + 2) =
          momentScalar (u + 2) / ((u + 2 : ℕ) : ℚ) := by
        have hu : (u : ℚ) + 2 ≠ 0 := by positivity
        push_cast at hrec ⊢
        field_simp [hu]
        nlinarith only [hrec]
      simpa only [smoothingTerm, Nat.zero_add,
        show 1 + (u + 1) = u + 2 by omega,
        show u + 1 + 1 = u + 2 by omega,
        Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using
          congrArg (fun x : ℚ => (x : ℚ_[2])) hq
    · simp [smoothingTerm, momentScalar_odd 0]
  have hv := smoothing_hasSum_sub_add_two_value _ momentScalar_padic_tendsto_zero hs'
  simpa [momentScalar_odd 0] using hv

theorem smoothingMoment_second_boundary_step (d : ℕ) :
    ((d + 1 : ℕ) : ℚ_[2]) * smoothingMoment 0 (d + 2) =
      (d : ℚ_[2]) * smoothingMoment 0 d + 2 / ((d + 1 : ℕ) : ℚ_[2]) := by
  have htail := (hasSum_nat_add_iff' 2).mpr (smoothingMoment_hasSum 0 d)
  have htail' : HasSum
      (fun u => ((momentScalar (u + 2) / ((d + u + 3 : ℕ) : ℚ) : ℚ) : ℚ_[2]))
      (smoothingMoment 0 d - 2 / ((d + 1 : ℕ) : ℚ_[2])) := by
    convert htail using 1
    · ext u
      simp only [smoothingTerm, Nat.zero_add,
        show d + (u + 2) + 1 = d + u + 3 by omega]
    · simp [smoothingTerm, Finset.sum_range_succ, momentScalar_odd 0]
  have hs := ((smoothingMoment_hasSum 0 (d + 2)).mul_left
      ((d + 1 : ℕ) : ℚ_[2])).sub (htail'.mul_left (d : ℚ_[2]))
  have hs' : HasSum
      (fun u => (momentScalar u : ℚ_[2]) - (momentScalar (u + 2) : ℚ_[2]))
      (((d + 1 : ℕ) : ℚ_[2]) * smoothingMoment 0 (d + 2) -
        (d : ℚ_[2]) * (smoothingMoment 0 d - 2 / ((d + 1 : ℕ) : ℚ_[2]))) := by
    convert hs using 1
    ext u
    have hrec := smoothingScalar_step u
    have hq : momentScalar u - momentScalar (u + 2) =
        ((d + 1 : ℕ) : ℚ) * (momentScalar u / ((d + u + 3 : ℕ) : ℚ)) -
        (d : ℚ) * (momentScalar (u + 2) / ((d + u + 3 : ℕ) : ℚ)) := by
      have hu : (d : ℚ) + u + 3 ≠ 0 := by positivity
      push_cast at hrec ⊢
      field_simp [hu]
      nlinarith only [hrec]
    simpa only [smoothingTerm, Nat.zero_add,
      show d + 2 + u + 1 = d + u + 3 by omega,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] using
        congrArg (fun x : ℚ => (x : ℚ_[2])) hq
  have hv := smoothing_hasSum_sub_add_two_value _ momentScalar_padic_tendsto_zero hs'
  have hd : (d : ℚ_[2]) + 1 ≠ 0 := by
    exact_mod_cast (show (d : ℚ) + 1 ≠ 0 by positivity)
  simp only [momentScalar_zero, momentScalar_odd 0, Rat.cast_ofNat,
    Rat.cast_zero, add_zero] at hv
  push_cast at hv ⊢
  field_simp [hd] at hv ⊢
  linear_combination hv

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

theorem smoothingMoment_minus_decomposition (d : ℕ) :
    smoothingMoment (d) (0) = (boundaryMinus d : ℚ_[2]) +
      smoothingMoment 0 0 * (centralCoeffKernel (d : ℤ) : ℚ_[2]) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => simp
    | succ d =>
      cases d with
      | zero =>
        simpa [centralCoeffKernel] using smoothingMoment_one_zero
      | succ d =>
        change smoothingMoment ((d + 2)) (0) = (boundaryMinus (d + 2) : ℚ_[2]) +
          smoothingMoment 0 0 * (centralCoeffKernel ((d + 2 : ℕ) : ℤ) : ℚ_[2])
        have ha := smoothingMoment_first_boundary_step d
        rw [ih d (by omega)] at ha
        have hr : ((d + 2 : ℕ) : ℚ_[2]) * (boundaryMinus (d + 2) : ℚ_[2]) =
            ((d + 1 : ℕ) : ℚ_[2]) * (boundaryMinus d : ℚ_[2]) +
              (momentScalar d : ℚ_[2]) + (momentScalar (d + 1) : ℚ_[2]) := by
          exact_mod_cast boundaryMinus_step d
        have hc : ((d + 2 : ℕ) : ℚ_[2]) *
              (centralCoeffKernel ((d + 2 : ℕ) : ℤ) : ℚ_[2]) =
            ((d + 1 : ℕ) : ℚ_[2]) * (centralCoeffKernel (d : ℤ) : ℚ_[2]) := by
          exact_mod_cast centralCoeffKernel_nat_step d
        have hstart := congrArg (fun x : ℚ_[2] => smoothingMoment 0 0 * x) hc
        have hd : ((d + 2 : ℕ) : ℚ_[2]) ≠ 0 := by
          exact_mod_cast (show ((d + 2 : ℕ) : ℚ) ≠ 0 by positivity)
        apply mul_left_cancel₀ hd
        linear_combination ha - hr - hstart

theorem smoothingMoment_plus_succ_decomposition (u : ℕ) :
    smoothingMoment (0) ((u + 1)) = (boundaryPlus (u + 1) : ℚ_[2]) +
      smoothingMoment 0 1 * (centralCoeffKernel (u : ℤ) : ℚ_[2]) := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero => simp
    | succ u =>
      cases u with
      | zero =>
        have ha := smoothingMoment_second_boundary_step 0
        norm_num at ha
        simpa [boundaryPlus, centralCoeffKernel] using ha
      | succ u =>
        change smoothingMoment (0) ((u + 2 + 1)) =
          (boundaryPlus (u + 2 + 1) : ℚ_[2]) +
            smoothingMoment 0 1 * (centralCoeffKernel ((u + 2 : ℕ) : ℤ) : ℚ_[2])
        have ha := smoothingMoment_second_boundary_step (u + 1)
        rw [ih u (by omega)] at ha
        have hr : ((u + 1 + 1 : ℕ) : ℚ_[2]) * (boundaryPlus (u + 1 + 2) : ℚ_[2]) =
            ((u + 1 : ℕ) : ℚ_[2]) * (boundaryPlus (u + 1) : ℚ_[2]) +
              2 / ((u + 1 + 1 : ℕ) : ℚ_[2]) := by
          have hr0 := congrArg (fun x : ℚ => (x : ℚ_[2])) (boundaryPlus_step (u + 1))
          push_cast at hr0 ⊢
          exact hr0
        have hc : ((u + 2 : ℕ) : ℚ_[2]) *
              (centralCoeffKernel ((u + 2 : ℕ) : ℤ) : ℚ_[2]) =
            ((u + 1 : ℕ) : ℚ_[2]) * (centralCoeffKernel (u : ℤ) : ℚ_[2]) := by
          exact_mod_cast centralCoeffKernel_nat_step u
        have hstart := congrArg (fun x : ℚ_[2] => smoothingMoment 0 1 * x) hc
        have hu : ((u + 2 : ℕ) : ℚ_[2]) ≠ 0 := by
          exact_mod_cast (show ((u + 2 : ℕ) : ℚ) ≠ 0 by positivity)
        apply mul_left_cancel₀ hu
        linear_combination ha - hr - hstart

theorem smoothingMoment_decomposition (i j : ℕ) :
    smoothingMoment (i) (j) = (momentRat i j : ℚ_[2]) +
      smoothingMoment 0 0 * (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]) +
      smoothingMoment 0 1 * (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℚ_[2]) := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => norm_num [centralCoeffKernel]
    | succ j =>
      have hn : centralCoeffKernel ((0 : ℤ) - ((j + 1 : ℕ) : ℤ)) = 0 :=
        centralCoeffKernel_of_neg (by omega)
      have he : ((j + 1 : ℕ) : ℤ) - (0 : ℤ) - 1 = (j : ℤ) := by omega
      simp only [Nat.cast_zero]
      rw [momentRat_zero_left, hn, he]
      simpa using smoothingMoment_plus_succ_decomposition j
  | succ i ih =>
    cases j with
    | zero =>
      have hn : centralCoeffKernel ((0 : ℤ) - ((i + 1 : ℕ) : ℤ) - 1) = 0 :=
        centralCoeffKernel_of_neg (by omega)
      simp only [Nat.cast_zero]
      rw [momentRat_zero_right, hn]
      simpa using smoothingMoment_minus_decomposition (i + 1)
    | succ j =>
      have ha := smoothingMoment_step i j
      have hr : (momentRat i j : ℚ_[2]) - (momentRat (i + 1) (j + 1) : ℚ_[2]) =
          (momentScalar i : ℚ_[2]) / ((j + 1 : ℕ) : ℚ_[2]) := by
        exact_mod_cast momentRat_step i j
      have hd : ((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) =
          (i : ℤ) - (j : ℤ) := by omega
      have he : ((j + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) - 1 =
          (j : ℤ) - (i : ℤ) - 1 := by omega
      change smoothingMoment ((i + 1)) ((j + 1)) =
        (momentRat (i + 1) (j + 1) : ℚ_[2]) +
          smoothingMoment 0 0 * (centralCoeffKernel (((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) : ℚ_[2]) +
          smoothingMoment 0 1 *
            (centralCoeffKernel (((j + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) - 1) : ℚ_[2])
      rw [hd, he]
      rw [ih j] at ha
      push_cast at ha hr
      linear_combination hr - ha

theorem smoothingMoment_discrepancies (q : ℚ) (i j : ℕ) :
    (momentRat i j : ℚ_[2]) + (4 * (q : ℚ_[2])) *
        (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]) =
      smoothingMoment i j +
        (4 * (q : ℚ_[2]) - smoothingMoment 0 0) *
          (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℚ_[2]) +
        (-smoothingMoment 0 1) *
          (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℚ_[2]) := by
  rw [smoothingMoment_decomposition]
  ring

end InternalCatalan

end

end OAI

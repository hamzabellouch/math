import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.InitialLeafRates
import OAI.LinearAlgebra.MatrixFields.Extraction.ComplexLabelHierarchySeparation
import OAI.LinearAlgebra.MatrixFields.Extraction.ComplexRationalTypes

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology

noncomputable def factorialLogRemainder (n : ℕ) : ℝ :=
  Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n)

theorem factorialLogRemainder_eq (n : ℕ) :
    factorialLogRemainder n =
      Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n) := rfl

@[simp] theorem factorialLogRemainder_zero : factorialLogRemainder 0 = 0 := by
  simp [factorialLogRemainder]

theorem factorialLogRemainder_stirling (n : ℕ) :
    factorialLogRemainder n =
      Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log (2 * n) := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Stirling.log_stirlingSeq_formula (n + 1)
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
    unfold factorialLogRemainder
    linarith

theorem tendsto_factorialLogRemainder_div :
    Tendsto (fun n : ℕ => factorialLogRemainder n / (n : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hstirling :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
        atTop (𝓝 0) :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hconstant : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using hstirling.add ((hconstant.add hlog).const_mul (1 / 2 : ℝ))
  apply hsum.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  rw [factorialLogRemainder_stirling,
    Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn)]
  ring

theorem tendsto_factorialLogRemainder_mul_div (c : ℕ) :
    Tendsto (fun t : ℕ => factorialLogRemainder (t * c) / (t : ℝ))
      atTop (𝓝 0) := by
  by_cases hc : c = 0
  · subst c
    simp
  have hmul : Tendsto (fun t : ℕ => t * c) atTop atTop :=
    tendsto_id.atTop_mul_const' (Nat.pos_of_ne_zero hc)
  have hscaled : Tendsto
      (fun t : ℕ => factorialLogRemainder (t * c) / (t * c : ℕ) * (c : ℝ))
      atTop (𝓝 0) := by
    simpa using (tendsto_factorialLogRemainder_div.comp hmul).mul_const (c : ℝ)
  apply hscaled.congr
  intro t
  by_cases ht : t = 0
  · simp [ht]
  rw [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr hc, Nat.cast_ne_zero.mpr ht]

theorem factorialLogRemainder_succ (n : ℕ) :
    factorialLogRemainder (n + 1) = factorialLogRemainder n + 1 -
      (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  unfold factorialLogRemainder
  rw [Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

private theorem nat_mul_log_increment_le_one (n : ℕ) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have heq : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
    field_simp [hpos.ne']
    ring
  rwa [heq] at hmul

private theorem one_le_succ_mul_log_increment (n : ℕ) (hn : 0 < n) :
    1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hsucc.le
  have heq : ((n : ℝ) + 1) * (1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹) = 1 := by
    rw [inv_div]
    field_simp [hsucc.ne']
    ring
  rwa [heq] at hmul

theorem factorialLogRemainder_nonneg (n : ℕ) : 0 ≤ factorialLogRemainder n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlog := nat_mul_log_increment_le_one n
    rw [factorialLogRemainder_succ]
    linarith

theorem factorialLogRemainder_le_one_add_log_pos (n : ℕ) :
    factorialLogRemainder (n + 1) ≤ 1 + Real.log (n + 1 : ℕ) := by
  induction n with
  | zero => norm_num [factorialLogRemainder]
  | succ n ih =>
    have hlog := one_le_succ_mul_log_increment (n + 1) (Nat.succ_pos n)
    have hstep := factorialLogRemainder_succ (n + 1)
    push_cast at ih hlog hstep ⊢
    nlinarith

theorem factorialLogRemainder_le_one_add_log (n : ℕ) :
    factorialLogRemainder n ≤ 1 + Real.log (n + 1 : ℕ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    refine (factorialLogRemainder_le_one_add_log_pos n).trans ?_
    apply add_le_add le_rfl
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.le_succ (n + 1)

theorem abs_factorialLogRemainder_le (n : ℕ) :
    |factorialLogRemainder n| ≤ 1 + Real.log (n + 1 : ℕ) := by
  rw [abs_of_nonneg (factorialLogRemainder_nonneg n)]
  exact factorialLogRemainder_le_one_add_log n

end MatrixMultiplication.Foundation





namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]

theorem log_multinomial (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      Real.log (Nat.factorial (∑ a, counts a) : ℝ) -
        ∑ a, Real.log (Nat.factorial (counts a) : ℝ) := by
  have hspec :
      (∏ a, (Nat.factorial (counts a) : ℝ)) *
          (Nat.multinomial Finset.univ counts : ℝ) =
        (Nat.factorial (∑ a, counts a) : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hprod : (∏ a, (Nat.factorial (counts a) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by positivity)
  have hmulti : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hlog := congrArg Real.log hspec
  rw [Real.log_mul hprod hmulti,
    Real.log_prod (fun a _ => by positivity)] at hlog
  linarith

private theorem entropyTerm_div_scalar (x y : ℝ) :
    entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [entropyTerm, Real.log_div hx hy]
  unfold entropyTerm
  ring

theorem finiteEntropy_nat_normalize (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) /
          (∑ a, counts a : ℕ) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  unfold finiteEntropy
  simp only [entropyTerm_div_scalar]
  simp only [entropyTerm, neg_mul,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  rw [← Nat.cast_sum, div_self hD']
  ring

theorem log_multinomial_eq_main_add_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  rw [log_multinomial]
  unfold factorialLogRemainder
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
  ring

theorem log_multinomial_eq_entropy_add_remainder (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  rw [log_multinomial_eq_main_add_remainder, finiteEntropy_nat_normalize counts hD,
    mul_sub, mul_div_cancel₀ _ hD']

theorem log_multinomial_sub_entropy_eq_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  by_cases hD : 0 < ∑ a, counts a
  · rw [log_multinomial_eq_entropy_add_remainder counts hD]
    ring
  · have hzero : (∑ a, counts a) = 0 := Nat.eq_zero_of_not_pos hD
    have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, Nat.multinomial]

theorem abs_log_multinomial_sub_entropy_le (counts : A → ℕ) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  rw [log_multinomial_sub_entropy_eq_remainder]
  have hsum_nonneg : 0 ≤ ∑ a, factorialLogRemainder (counts a) :=
    Finset.sum_nonneg (fun a _ => factorialLogRemainder_nonneg (counts a))
  have heach (a : A) : factorialLogRemainder (counts a) ≤
      1 + Real.log ((∑ b, counts b) + 1 : ℕ) := by
    refine (factorialLogRemainder_le_one_add_log (counts a)).trans ?_
    apply add_le_add le_rfl
    apply Real.log_le_log
    · positivity
    · have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      exact_mod_cast Nat.add_le_add_right hle 1
  calc
    |factorialLogRemainder (∑ a, counts a) - ∑ a, factorialLogRemainder (counts a)| ≤
        |factorialLogRemainder (∑ a, counts a)| +
          |∑ a, factorialLogRemainder (counts a)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (factorialLogRemainder (∑ a, counts a))
          (-(∑ a, factorialLogRemainder (counts a)))
    _ = factorialLogRemainder (∑ a, counts a) +
        ∑ a, factorialLogRemainder (counts a) := by
      rw [abs_of_nonneg (factorialLogRemainder_nonneg _), abs_of_nonneg hsum_nonneg]
    _ ≤ (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) +
        ∑ _a : A, (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) :=
      add_le_add (factorialLogRemainder_le_one_add_log _)
        (Finset.sum_le_sum (fun a _ => heach a))
    _ = ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem abs_log_multinomial_div_sub_entropy_le (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  calc
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| =
        |(Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))) /
              (∑ a, counts a : ℕ)| := by
      rw [sub_div, mul_div_cancel_left₀ _ hD'.ne']
    _ = |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| /
              (∑ a, counts a : ℕ) := by
      rw [abs_div, abs_of_pos hD']
    _ ≤ ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (abs_log_multinomial_sub_entropy_le counts) hD'.le

private theorem tendsto_one_add_log_succ_div :
    Tendsto (fun n : ℕ => (1 + Real.log (n + 1 : ℕ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconstant : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hshift := Real.tendsto_log_nat_add_one_sub_log.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => (1 : ℝ) / n +
        ((Real.log ((n : ℝ) + 1) - Real.log n) / n + Real.log n / n))
      atTop (𝓝 0) := by
    simpa using hconstant.add (hshift.add hlog)
  apply hsum.congr
  intro n
  push_cast
  ring

theorem tendsto_log_multinomial_div_sub_entropy {I : Type*} {l : Filter I}
    (counts : I → A → ℕ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
          (∑ a, counts i a : ℕ) -
        finiteEntropy (fun a => (counts i a : ℝ) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
  have hbound : Tendsto
      (fun i => ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts i a) + 1 : ℕ)) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
    simpa using (tendsto_one_add_log_succ_div.comp htotal).const_mul
      ((Fintype.card A : ℝ) + 1)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [htotal.eventually (eventually_gt_atTop (0 : ℕ))] with i hi
  simpa only [Real.norm_eq_abs] using
    abs_log_multinomial_div_sub_entropy_le (counts i) hi

theorem tendsto_log_multinomial_of_empirical_tendsto {I : Type*} {l : Filter I}
    (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  have herror := tendsto_log_multinomial_div_sub_entropy counts htotal
  have hentropy := tendsto_finiteEntropy_of_tendsto hmass
  simpa only [zero_add, sub_add_cancel] using herror.add hentropy

private theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) =
      (x * Real.log x) * y + x * (y * Real.log y) := by
  calc
    (x * y) * Real.log (x * y) = -entropyTerm (x * y) := by
      simp [entropyTerm]
    _ = -(y * entropyTerm x + x * entropyTerm y) := by
      rw [entropyTerm_mul]
    _ = (x * Real.log x) * y + x * (y * Real.log y) := by
      unfold entropyTerm
      ring

theorem log_multinomial_mul_eq (counts : A → ℕ) (t : ℕ) :
    Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) =
      (t : ℝ) *
          ((∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
            ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (t * ∑ a, counts a) -
        ∑ a, factorialLogRemainder (t * counts a) := by
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a :=
    (Finset.mul_sum Finset.univ counts t).symm
  have hlogs :
      (∑ a, ((t : ℝ) * counts a) * Real.log ((t : ℝ) * counts a)) =
        ((t : ℝ) * Real.log t) * (∑ a, counts a : ℕ) +
          (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ) := by
    simp only [mul_log_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Nat.cast_sum]
  rw [log_multinomial_eq_main_add_remainder, hsum]
  simp only [Nat.cast_mul]
  rw [mul_log_mul, hlogs]
  ring

theorem tendsto_log_multinomial_mul (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  have hsum :
      Tendsto (fun t : ℕ => ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ))
        atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ
      (fun a _ => tendsto_factorialLogRemainder_mul_div (counts a))
  have herror : Tendsto
      (fun t : ℕ =>
        (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
          ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
            (∑ a, counts a : ℕ)) atTop (𝓝 0) := by
    simpa using ((tendsto_factorialLogRemainder_mul_div (∑ a, counts a)).sub
      hsum).div_const (∑ a, counts a : ℕ)
  have hlimit : Tendsto
      (fun t : ℕ =>
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
          (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
            ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
              (∑ a, counts a : ℕ))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  apply hlimit.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  rw [log_multinomial_mul_eq, finiteEntropy_nat_normalize counts hD,
    ← Finset.sum_div]
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  field_simp [ht', hD']
  ring

theorem tendsto_log_multinomial_repetitions {I : Type*} {l : Filter I}
    (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (repetitions : I → ℕ) (hrep : Tendsto repetitions l atTop) :
    Tendsto
      (fun i =>
        Real.log (Nat.multinomial Finset.univ
          (fun a => repetitions i * counts a) : ℝ) /
            ((repetitions i : ℝ) * (∑ a, counts a : ℕ)))
      l (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  exact (tendsto_log_multinomial_mul counts hD).comp hrep

theorem tendsto_log_exactWords_card_mul [DecidableEq A] (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [exactWords_card] using tendsto_log_multinomial_mul counts hD

theorem abs_log_exactWords_card_sub_entropy_le [DecidableEq A] (counts : A → ℕ) :
    |Real.log (Fintype.card (ExactWords counts) : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  simpa only [exactWords_card] using abs_log_multinomial_sub_entropy_le counts

theorem log_card_le_entropy_of_injective_exactWords [DecidableEq A]
    {O : Type*} [Fintype O] [Nonempty O] (counts : A → ℕ)
    (label : O → ExactWords counts) (hinj : Function.Injective label) :
    Real.log (Fintype.card O : ℝ) ≤
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ((Fintype.card A : ℝ) + 1) *
          (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  have hcard := Fintype.card_le_of_injective label hinj
  have hlog : Real.log (Fintype.card O : ℝ) ≤
      Real.log (Fintype.card (ExactWords counts) : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr Fintype.card_pos) (by exact_mod_cast hcard)
  have herror := (abs_le.mp (abs_log_exactWords_card_sub_entropy_le counts)).2
  linarith

theorem log_card_div_le_entropy_of_injective_exactWords [DecidableEq A]
    {O : Type*} [Fintype O] [Nonempty O] (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a)
    (label : O → ExactWords counts) (hinj : Function.Injective label) :
    Real.log (Fintype.card O : ℝ) / (∑ a, counts a : ℕ) ≤
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ((Fintype.card A : ℝ) + 1) *
          ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  have h := div_le_div_of_nonneg_right
    (log_card_le_entropy_of_injective_exactWords counts label hinj) hD'.le
  rw [add_div, mul_div_cancel_left₀ _ hD'.ne', mul_div_assoc] at h
  exact h

theorem tendsto_log_exactWords_card_of_empirical_tendsto [DecidableEq A]
    {I : Type*} {l : Filter I} (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Fintype.card (ExactWords (counts i)) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  simpa only [exactWords_card] using
    tendsto_log_multinomial_of_empirical_tendsto counts p htotal hmass

namespace RationalLaw

theorem exists_exactWords_entropy_limit [DecidableEq A] (p : RationalLaw A) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      (∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a) ∧
      Tendsto
        (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) := by
  obtain ⟨counts, hD, hmass⟩ := p.exists_type_representation
  refine ⟨counts, hD, hmass, ?_⟩
  have hfun : (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      p.toFiniteLaw.mass := funext hmass
  rw [← hfun]
  exact tendsto_log_exactWords_card_mul counts hD

end RationalLaw

end MatrixMultiplication.Foundation





noncomputable section

namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

namespace LabelHierarchySeparation

theorem poolAuxiliaryCost_pos (k : ℕ) : 0 < poolAuxiliaryCost k := by
  unfold poolAuxiliaryCost
  split_ifs
  · exact Nat.zero_lt_one
  · exact Separation.gridGroupOrder_pos k

theorem population_le_poolAuxiliaryCost (k : ℕ) : k ≤ poolAuxiliaryCost k := by
  unfold poolAuxiliaryCost
  split_ifs with hk
  · simp [hk]
  · exact Separation.population_le_gridGroupOrder k

theorem poolAuxiliaryCost_le_gridGroupOrder (k : ℕ) :
    poolAuxiliaryCost k ≤ Separation.gridGroupOrder k := by
  unfold poolAuxiliaryCost
  split_ifs with hk
  · simpa only [hk] using Separation.population_le_gridGroupOrder k
  · exact le_rfl

theorem tendsto_log_poolAuxiliaryCost_div_nat {K : ℕ → ℕ} {H : ℝ}
    (hK : ∀ n, 0 < K n) (hH : 0 ≤ H)
    (hpop : Tendsto (fun n => Real.log (K n : ℝ) / (n : ℝ)) atTop (𝓝 H)) :
    Tendsto (fun n => Real.log (poolAuxiliaryCost (K n) : ℝ) / (n : ℝ))
      atTop (𝓝 H) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hpop
    (Separation.tendsto_log_gridGroupOrder_div_nat hK hH hpop) ?_ ?_
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.log_le_log (Nat.cast_pos.mpr (hK n))
      (by exact_mod_cast population_le_poolAuxiliaryCost (K n))
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.log_le_log (Nat.cast_pos.mpr (poolAuxiliaryCost_pos (K n)))
      (by exact_mod_cast poolAuxiliaryCost_le_gridGroupOrder (K n))

end LabelHierarchySeparation

namespace HierarchySeparationRates

universe u v w

def populationEntropyRate {B : Type*} [Fintype B] (counts : B → ℕ) : ℝ :=
  (∑ b, counts b : ℕ) *
    finiteEntropy (fun b => (counts b : ℝ) / (∑ b, counts b : ℕ))

theorem tendsto_log_multinomial_mul_div_repetition {B : Type*} [Fintype B]
    (counts : B → ℕ) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun b => t * counts b) : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts)) := by
  by_cases hD : 0 < ∑ b, counts b
  · have hD' : ((∑ b, counts b : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
    have h := (tendsto_log_multinomial_mul counts hD).const_mul
      ((∑ b, counts b : ℕ) : ℝ)
    apply h.congr
    intro t
    by_cases ht : t = 0
    · simp [ht]
    have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
    change ((∑ b, counts b : ℕ) : ℝ) *
        (Real.log (Nat.multinomial Finset.univ (fun b => t * counts b) : ℝ) /
          ((t : ℝ) * (∑ b, counts b : ℕ))) = _
    field_simp [hD', ht']
  · have hz : (∑ b, counts b) = 0 := Nat.eq_zero_of_not_pos hD
    have hc (b : B) : counts b = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc
        counts b ≤ ∑ c, counts c :=
          Finset.single_le_sum (fun c _ => Nat.zero_le _) (Finset.mem_univ b)
        _ = 0 := hz
    simp only [populationEntropyRate, hz, Nat.cast_zero, zero_mul]
    simp [Nat.multinomial, hc]

theorem populationEntropyRate_nonneg {B : Type*} [Fintype B] (counts : B → ℕ) :
    0 ≤ populationEntropyRate counts := by
  apply ge_of_tendsto' (tendsto_log_multinomial_mul_div_repetition counts)
  intro t
  apply div_nonneg _ (Nat.cast_nonneg t)
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ (fun b => t * counts b)))

section FinitePools

variable {I : Type u} [Fintype I] {Alphabet : I → Type v}
  [∀ i, Fintype (Alphabet i)]

def poolTypeCount (counts : ∀ i, Alphabet i → ℕ) (i : I) (t : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (fun b => t * counts i b)

def poolEntropyTotal (counts : ∀ i, Alphabet i → ℕ) : ℝ :=
  ∑ i, populationEntropyRate (counts i)

def pairingProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, poolTypeCount counts i t

def gridProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, Separation.gridGroupOrder (poolTypeCount counts i t)

def auxiliaryProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, LabelHierarchySeparation.poolAuxiliaryCost (poolTypeCount counts i t)

omit [Fintype I] in
theorem poolTypeCount_pos (counts : ∀ i, Alphabet i → ℕ) (i : I) (t : ℕ) :
    0 < poolTypeCount counts i t := Nat.multinomial_pos _ _

theorem pairingProduct_le_auxiliaryProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) :
    pairingProduct counts t ≤ auxiliaryProduct counts t := by
  exact Finset.prod_le_prod (fun i _ =>
    LabelHierarchySeparation.population_le_poolAuxiliaryCost (poolTypeCount counts i t))

theorem auxiliaryProduct_le_gridProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) :
    auxiliaryProduct counts t ≤ gridProduct counts t := by
  exact Finset.prod_le_prod (fun i _ =>
    LabelHierarchySeparation.poolAuxiliaryCost_le_gridGroupOrder (poolTypeCount counts i t))

omit [Fintype I] in
theorem tendsto_log_poolTypeCount_div (counts : ∀ i, Alphabet i → ℕ) (i : I) :
    Tendsto (fun t : ℕ => Real.log (poolTypeCount counts i t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate (counts i))) :=
  tendsto_log_multinomial_mul_div_repetition (counts i)

theorem tendsto_log_pairingProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (pairingProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun i _ t => poolTypeCount_pos counts i t)
    (fun i _ => tendsto_log_poolTypeCount_div counts i)

theorem tendsto_log_gridProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (gridProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_gridGroupOrder_prod_div_nat Finset.univ
    (fun i _ t => poolTypeCount_pos counts i t)
    (fun i _ => populationEntropyRate_nonneg (counts i))
    (fun i _ => tendsto_log_poolTypeCount_div counts i)

theorem tendsto_log_auxiliaryProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (auxiliaryProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun i _ t => LabelHierarchySeparation.poolAuxiliaryCost_pos (poolTypeCount counts i t))
    (fun i _ => LabelHierarchySeparation.tendsto_log_poolAuxiliaryCost_div_nat
      (poolTypeCount_pos counts i) (populationEntropyRate_nonneg (counts i))
      (tendsto_log_poolTypeCount_div counts i))

end FinitePools

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

theorem pushforwardCounts_mul {B : Type*} (counts : A → ℕ) (label : A → B)
    (t : ℕ) (b : B) :
    pushforwardCounts (fun a => t * counts a) label b =
      t * pushforwardCounts counts label b := by
  classical
  unfold pushforwardCounts
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : label a = b <;> simp [h]

omit [∀ n, Fintype (Label n)] in
theorem sourcePrefixCounts_mul (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (t n : ℕ) (r : LabelRecord Label n) :
    LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a) labels n r =
      t * LabelHierarchyCounts.sourcePrefixCounts counts labels n r :=
  pushforwardCounts_mul counts (labelRecordOf labels n) t r

abbrev PrefixPool (Label : ℕ → Type v) (depth : ℕ) :=
  Σ n : Fin depth, LabelRecord Label n.val

def sourcePoolCounts (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (j : PrefixPool Label depth) (s : Label j.1.val) : ℕ :=
  LabelHierarchyCounts.sourcePrefixCounts counts labels (j.1.val + 1) (j.2, s)

theorem pairingProduct_source_eq (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    pairingProduct (sourcePoolCounts counts labels depth) t =
      Nat.multinomial Finset.univ (fun a => t * counts a) := by
  classical
  unfold pairingProduct
  rw [Fintype.prod_sigma]
  have hpool (n : Fin depth) :
      (∏ r : LabelRecord Label n.val,
        poolTypeCount (sourcePoolCounts counts labels depth) ⟨n, r⟩ t) =
      LabelHierarchyCounts.refinementCount
        (LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a) labels) n.val := by
    apply Finset.prod_congr rfl
    intro r _
    change Nat.multinomial Finset.univ
        (fun s : Label n.val => t *
          LabelHierarchyCounts.sourcePrefixCounts counts labels (n.val + 1) (r, s)) =
      Nat.multinomial Finset.univ
        (fun s : Label n.val =>
          LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a)
            labels (n.val + 1) (r, s))
    apply Nat.multinomial_congr
    intro s _
    exact (sourcePrefixCounts_mul counts labels t (n.val + 1) (r, s)).symm
  simp_rw [hpool]
  rw [Fin.prod_univ_eq_prod_range]
  exact LabelHierarchyCounts.source_refinementCount_product
    (fun a => t * counts a) labels depth hinjective

theorem pairingProduct_source_eq_exactWords_card [DecidableEq A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    pairingProduct (sourcePoolCounts counts labels depth) t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [pairingProduct_source_eq counts labels depth hinjective, exactWords_card]

theorem source_poolEntropyTotal_eq (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth)) :
    poolEntropyTotal (sourcePoolCounts counts labels depth) = populationEntropyRate counts := by
  have hsource : Tendsto
      (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        (t : ℝ)) atTop (𝓝 (populationEntropyRate counts)) := by
    simpa only [pairingProduct_source_eq counts labels depth hinjective] using
      tendsto_log_multinomial_mul_div_repetition counts
  exact tendsto_nhds_unique
    (tendsto_log_pairingProduct_div (sourcePoolCounts counts labels depth)) hsource

private theorem normalized_of_per_repetition (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (K : ℕ → ℕ)
    (h : Tendsto (fun t : ℕ => Real.log (K t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts))) :
    Tendsto (fun t : ℕ => Real.log (K t : ℝ) / ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hmain : populationEntropyRate counts / (∑ a, counts a : ℕ) =
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    unfold populationEntropyRate
    exact mul_div_cancel_left₀ _ hD'
  simpa only [div_div, hmain] using h.div_const ((∑ a, counts a : ℕ) : ℝ)

theorem tendsto_log_source_pairingProduct (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [pairingProduct_source_eq counts labels depth hinjective] using
    tendsto_log_multinomial_mul counts hD

theorem tendsto_log_source_gridProduct (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (gridProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  apply normalized_of_per_repetition counts hD
  simpa only [source_poolEntropyTotal_eq counts labels depth hinjective] using
    tendsto_log_gridProduct_div (sourcePoolCounts counts labels depth)

theorem tendsto_log_source_auxiliaryProduct (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (auxiliaryProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  apply normalized_of_per_repetition counts hD
  simpa only [source_poolEntropyTotal_eq counts labels depth hinjective] using
    tendsto_log_auxiliaryProduct_div (sourcePoolCounts counts labels depth)

theorem rationalLaw_exists_source_rates [DecidableEq A] (p : RationalLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    ∃ counts : A → ℕ, 0 < ∑ a, counts a ∧
      (∀ a, (counts a : ℝ) / (∑ a, counts a : ℕ) = p.toFiniteLaw.mass a) ∧
      Tendsto
        (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) ∧
      Tendsto
        (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) ∧
      Tendsto
        (fun t : ℕ => Real.log (gridProduct (sourcePoolCounts counts labels depth) t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) ∧
      Tendsto
        (fun t : ℕ => Real.log (auxiliaryProduct (sourcePoolCounts counts labels depth) t : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
        atTop (𝓝 (finiteEntropy p.toFiniteLaw.mass)) := by
  obtain ⟨counts, hD, hmass⟩ := p.exists_type_representation
  have hfun : (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      p.toFiniteLaw.mass := funext hmass
  refine ⟨counts, hD, hmass, ?_, ?_, ?_, ?_⟩
  · simpa only [hfun] using tendsto_log_exactWords_card_mul counts hD
  · simpa only [hfun] using tendsto_log_source_pairingProduct counts hD labels depth hinjective
  · simpa only [hfun] using tendsto_log_source_gridProduct counts hD labels depth hinjective
  · simpa only [hfun] using tendsto_log_source_auxiliaryProduct counts hD labels depth hinjective

end SourceHierarchy

end HierarchySeparationRates
end MatrixMultiplication.Foundation






namespace MatrixMultiplication.LeafRates

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

variable {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]

omit [DecidableEq U] in
theorem log_card_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) :
    Real.log (Fintype.card (ExactStatisticWords.Words statistic counts) : ℝ) =
      Real.log (Nat.multinomial Finset.univ counts : ℝ) +
        ∑ a, (counts a : ℝ) * Real.log (b a : ℝ) := by
  rw [ExactStatisticWords.card_of_supported statistic counts b hb, Nat.cast_mul, Nat.cast_prod]
  have hm : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hp : (∏ a, (b a ^ counts a : ℕ) : ℝ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    exact_mod_cast (Nat.ne_of_gt (pow_pos (hbpos a) _))
  rw [Real.log_mul hm hp, Real.log_prod
    (fun a _ => by exact_mod_cast (Nat.ne_of_gt (pow_pos (hbpos a) (counts a))))]
  simp only [Nat.cast_pow, Real.log_pow]

omit [DecidableEq U] in
theorem log_card (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) :
    Real.log (Fintype.card (ExactStatisticWords.Words statistic counts) : ℝ) =
      Real.log (Nat.multinomial Finset.univ counts : ℝ) +
        ∑ a, (counts a : ℝ) * Real.log (b a : ℝ) :=
  log_card_supported statistic counts b (fun a _ => hb a) hbpos

omit [DecidableEq U] in
theorem tendsto_log_card_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) (hD : 0 < ∑ a, counts a) :
    Tendsto (fun t : ℕ =>
      Real.log (Fintype.card (ExactStatisticWords.Words statistic (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (b a : ℝ))) := by
  have hl := (tendsto_log_multinomial_mul counts hD).add_const
    (∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (b a : ℝ))
  apply hl.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  have hbt : ∀ a, 0 < t * counts a → Fintype.card {u : U // statistic u = a} = b a :=
    fun a ha => hb a (by nlinarith)
  rw [log_card_supported statistic (fun a => t * counts a) b hbt hbpos, add_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hDsum : (∑ a, (counts a : ℝ)) ≠ 0 := by
    simpa only [Nat.cast_sum] using hD'
  simp only [Nat.cast_mul]
  field_simp [ht', hD', hDsum]

omit [DecidableEq U] in
theorem tendsto_log_card (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) (hD : 0 < ∑ a, counts a) :
    Tendsto (fun t : ℕ =>
      Real.log (Fintype.card (ExactStatisticWords.Words statistic (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (b a : ℝ))) :=
  tendsto_log_card_supported statistic counts b (fun a _ => hb a) hbpos hD

end MatrixMultiplication.LeafRates






namespace MatrixMultiplication.AllFieldZeroLeafRates

open MatrixMultiplication.Foundation Filter AllFieldParameters CWWindowedLeaves CWCompleteStatistics
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

abbrev fourWords (t : Shape) (counts : PairSlot → ℕ) (m : ℕ) :=
  ExactStatisticWords.Words
    (fun w : Alphabet 4 (shapeMax t) => fourStatistic w.val) (fun s => m * counts s)

def twoWords (k : Fin 5) (counts : Fin 6 → ℕ) (m : ℕ) :=
  ExactStatisticWords.Words
    (fun w : Alphabet 2 k.val => twoStatistic w.val) (fun s => m * counts s)

instance twoWordsFintype (k : Fin 5) (counts : Fin 6 → ℕ) (m : ℕ) :
    Fintype (twoWords k counts m) := by
  unfold twoWords
  infer_instance

theorem multiplicity_pos (s : Fin 6) : 0 < AllFieldParameters.multiplicity s := by
  fin_cases s <;> decide

theorem four_supported (t : Shape) (counts : PairSlot → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (zeroPairLaw t s.1 s.2 : ℝ)) (s : PairSlot) (hs : 0 < counts s) :
    Fintype.card {w : Alphabet 4 (shapeMax t) // fourStatistic w.val = s} =
      AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 := by
  apply four_fixedWeight_multiplicity
  by_contra hweight
  have hzero := zeroPairLaw_outside_support t s.1 s.2 hweight
  have hpos : (0 : ℝ) < (counts s : ℝ) / (∑ s, counts s : ℕ) :=
    div_pos (by exact_mod_cast hs) (by exact_mod_cast hD)
  rw [hlaw s, hzero, Rat.cast_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem two_supported (d : ℚ) (k : Fin 5) (counts : Fin 6 → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (statisticLaw d k s : ℝ)) (s : Fin 6) (hs : 0 < counts s) :
    Fintype.card {w : Alphabet 2 k.val // twoStatistic w.val = s} =
      AllFieldParameters.multiplicity s := by
  apply two_fixedWeight_multiplicity
  by_contra hweight
  have hzero := statisticLaw_outside_support d k s hweight
  have hpos : (0 : ℝ) < (counts s : ℝ) / (∑ s, counts s : ℕ) :=
    div_pos (by exact_mod_cast hs) (by exact_mod_cast hD)
  rw [hlaw s, hzero, Rat.cast_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem four_card_pos (t : Shape) (counts : PairSlot → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (zeroPairLaw t s.1 s.2 : ℝ)) (m : ℕ) :
    0 < Fintype.card (fourWords t counts m) := by
  apply ExactStatisticWords.card_pos_of_supported
    (fun w : Alphabet 4 (shapeMax t) => fourStatistic w.val) (fun s => m * counts s)
    (fun s => AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2)
  · intro s hs
    exact four_supported t counts hD hlaw s (Nat.pos_of_mul_pos_left hs)
  · intro s _
    exact Nat.mul_pos (multiplicity_pos s.1) (multiplicity_pos s.2)

theorem two_card_pos (d : ℚ) (k : Fin 5) (counts : Fin 6 → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (statisticLaw d k s : ℝ)) (m : ℕ) :
    0 < Fintype.card (twoWords k counts m) := by
  have h := ExactStatisticWords.card_pos_of_supported
    (fun w : Alphabet 2 k.val => twoStatistic w.val) (fun s => m * counts s)
    AllFieldParameters.multiplicity
    (fun s hs => two_supported d k counts hD hlaw s (Nat.pos_of_mul_pos_left hs))
    (fun s _ => multiplicity_pos s)
  rw [Fintype.card_eq_nat_card] at h ⊢
  exact h

theorem four_tendsto_log_card (t : Shape) (counts : PairSlot → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (zeroPairLaw t s.1 s.2 : ℝ)) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (fourWords t counts m) : ℝ) /
      ((m : ℝ) * (∑ s, counts s : ℕ))) atTop (𝓝 (fourRate t)) := by
  have h := LeafRates.tendsto_log_card_supported
    (fun w : Alphabet 4 (shapeMax t) => fourStatistic w.val) counts
    (fun s => AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2)
    (four_supported t counts hD hlaw)
    (fun s => Nat.mul_pos (multiplicity_pos s.1) (multiplicity_pos s.2)) hD
  simpa only [fourWords, hlaw, fourRate] using h

theorem two_tendsto_log_card (d : ℚ) (k : Fin 5) (counts : Fin 6 → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (statisticLaw d k s : ℝ)) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (twoWords k counts m) : ℝ) /
      ((m : ℝ) * (∑ s, counts s : ℕ))) atTop (𝓝 (statisticRate d k)) := by
  have h := LeafRates.tendsto_log_card_supported
    (fun w : Alphabet 2 k.val => twoStatistic w.val) counts AllFieldParameters.multiplicity
    (two_supported d k counts hD hlaw) multiplicity_pos hD
  simp only [Fintype.card_eq_nat_card] at h ⊢
  simpa only [twoWords, hlaw, statisticRate] using h

end MatrixMultiplication.AllFieldZeroLeafRates

end
end

end MatrixAllFields

end OAI

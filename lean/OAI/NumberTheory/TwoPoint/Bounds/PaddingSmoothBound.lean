import OAI.NumberTheory.TwoPoint.Bounds.PaddingSmoothMass
import Mathlib.Analysis.PSeries

namespace OAI

/-! The smooth-dilation cost averaged over the actual reciprocal padding
law is bounded by an absolute convergent product, uniformly in the pool. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingSmoothConstant : ℝ :=
  Real.exp ((4 / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))) *
    ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ))

lemma paddingSmoothConstant_pos : 0 < paddingSmoothConstant := Real.exp_pos _

lemma smooth_half_local_bound (p : ℕ) (hp : 2 ≤ p) :
    0 ≤ 4 / ((p : ℝ) + 4) * ((1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ - 1) ∧
    4 / ((p : ℝ) + 4) * ((1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ - 1) ≤
      (4 / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))) * (p : ℝ) ^ (-3 / 2 : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 < (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hp0 _
  have hr1 : (p : ℝ) ^ (-(1 / 2) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have h20 : 0 < (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) := by
    have hh := Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (-(1 / 2) : ℝ) < 0)
    linarith
  have hrle : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
  have hlocal : (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ - 1 =
      (p : ℝ) ^ (-(1 / 2) : ℝ) / (1 - (p : ℝ) ^ (-(1 / 2) : ℝ)) := by
    apply (eq_div_iff (ne_of_gt (sub_pos.mpr hr1))).mpr
    rw [sub_mul, inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr hr1)), one_mul]
    ring
  rw [hlocal]
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (4 / (p : ℝ)) *
        ((p : ℝ) ^ (-(1 / 2) : ℝ) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_left (by norm_num) hp0 (by linarith)
      · exact div_le_div_of_nonneg_left hr0.le h20 (by linarith)
      · positivity
      · positivity
    _ = _ := by
      rw [show (-3 / 2 : ℝ) = -1 + (-1 / 2) by norm_num,
        Real.rpow_add hp0, Real.rpow_neg_one]
      ring_nf

lemma padding_smooth_half_average_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) :
    (reciprocalPaddingLaw Q).average
      (fun b => smoothReciprocalProduct (paddingSelectedDivisor Q b).primeFactors
        (1 / 2 : ℝ)) ≤ paddingSmoothConstant := by
  rw [padding_smooth_reciprocal_average Q hQ]
  let c := 4 / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))
  let e : ℕ → ℝ := fun p => 4 / ((p : ℝ) + 4) *
    ((1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ - 1)
  have hc : 0 ≤ c := by
    dsimp [c]
    have hh := Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : (1 : ℝ) < 2) (by norm_num : (-(1 / 2) : ℝ) < 0)
    positivity
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hsum : (∑ p : Q, e p.val) ≤ c * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ) := by
    calc
      _ ≤ ∑ p : Q, c * (p.val : ℝ) ^ (-3 / 2 : ℝ) := by
        apply sum_le_sum
        intro p _
        exact (smooth_half_local_bound p.val (hQ p.val p.property).two_le).2
      _ = c * ∑ p ∈ Q, (p : ℝ) ^ (-3 / 2 : ℝ) := by
        rw [← mul_sum, sum_coe_sort Q (fun p : ℕ => (p : ℝ) ^ (-3 / 2 : ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum Q (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)) hc
  calc
    _ ≤ ∏ p : Q, Real.exp (e p.val) := by
      apply prod_le_prod₀
      · intro p _
        have hh := (smooth_half_local_bound p.val (hQ p.val p.property).two_le).1
        change 0 ≤ 1 + e p.val
        linarith
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (e p.val)
    _ = Real.exp (∑ p : Q, e p.val) := (Real.exp_sum _ _).symm
    _ ≤ paddingSmoothConstant := Real.exp_le_exp.mpr hsum

lemma padding_smooth_half_sum_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) :
    (∑ q ∈ retainedPrimeDivisors Q, (4 : ℝ) ^ q.primeFactors.card / (q : ℝ) *
      smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) ≤
      paddingTiltNormalizer Q * paddingSmoothConstant := by
  have he := padding_smooth_reciprocal_sum Q hQ (1 / 2 : ℝ)
  rw [← padding_smooth_reciprocal_average Q hQ] at he
  rw [he]
  exact mul_le_mul_of_nonneg_left (padding_smooth_half_average_le Q hQ)
    (paddingTiltNormalizer_pos Q).le

end TwoPointCorrelations

end OAI

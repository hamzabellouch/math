import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterSums
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Algebra.BigOperators.Module

namespace OAI

/-! The elementary exponential smoothing remainder. Its monotonicity
makes the error in a periodic-character convolution bounded independently
of the smoothing scale. -/

namespace TwoPointCorrelations

open Finset Filter Set
open scoped Classical Topology

noncomputable def mrtQuadraticRemainder (u : ℝ) : ℝ :=
  u⁻¹ - (Real.exp u - 1)⁻¹

lemma mrt_quadratic_remainder_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ mrtQuadraticRemainder u := by
  have he : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  exact sub_nonneg.mpr (by simpa only [one_div] using one_div_le_one_div_of_le hu he)

lemma mrt_quadratic_remainder_le_inv {u : ℝ} (hu : 0 < u) :
    mrtQuadraticRemainder u ≤ u⁻¹ := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  exact sub_le_self _ (inv_nonneg.mpr he.le)

lemma mrt_quadratic_remainder_le_one {u : ℝ} (hu : 0 < u) :
    mrtQuadraticRemainder u ≤ 1 := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
  have hprod : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  rw [hprod] at hm
  unfold mrtQuadraticRemainder
  rw [inv_eq_one_div, inv_eq_one_div]
  apply (sub_le_iff_le_add).mpr
  have hh : 1 + 1 / (Real.exp u - 1) = Real.exp u / (Real.exp u - 1) := by
    field_simp
    ring
  rw [hh]
  apply (div_le_div_iff₀ hu he).mpr
  nlinarith

lemma mrt_quadratic_exponential_square {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * Real.exp u ≤ (Real.exp u - 1) ^ 2 := by
  let E := Real.exp (u / 2)
  have hE : 0 < E := Real.exp_pos _
  have hs := mul_le_mul_of_nonneg_right
    (Real.self_le_sinh_iff.mpr (show 0 ≤ u / 2 by positivity)) hE.le
  have he2 : E ^ 2 = Real.exp u := by
    dsimp only [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hei : Real.exp (-(u / 2)) * E = 1 := by
    dsimp only [E]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [Real.sinh_eq] at hs
  have hlin : u * E ≤ Real.exp u - 1 := by
    dsimp only [E] at hs
    change Real.exp (u / 2) ^ 2 = _ at he2
    change Real.exp (-(u / 2)) * Real.exp (u / 2) = 1 at hei
    dsimp only [E]
    nlinarith only [hs, he2, hei]
  have hsq := (sq_le_sq₀ (mul_nonneg hu hE.le)
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hu))).mpr hlin
  rwa [mul_pow, he2] at hsq

lemma mrt_quadratic_remainder_hasDeriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt mrtQuadraticRemainder
      (Real.exp u / (Real.exp u - 1) ^ 2 - 1 / u ^ 2) u := by
  have he : Real.exp u - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu))
  have hh : HasDerivAt mrtQuadraticRemainder
      (-1 / u ^ 2 - -Real.exp u / (Real.exp u - 1) ^ 2) u :=
    ((hasDerivAt_id u).inv hu.ne').sub
    (((Real.hasDerivAt_exp u).sub_const 1).inv he)
  convert hh using 1
  ring

lemma mrt_quadratic_remainder_deriv_nonpos {u : ℝ} (hu : 0 < u) :
    Real.exp u / (Real.exp u - 1) ^ 2 - 1 / u ^ 2 ≤ 0 := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  apply sub_nonpos.mpr
  apply (div_le_div_iff₀ (sq_pos_of_pos he) (sq_pos_of_pos hu)).mpr
  simpa only [mul_one, one_mul, mul_comm] using mrt_quadratic_exponential_square hu.le

lemma mrt_quadratic_remainder_antitone : AntitoneOn mrtQuadraticRemainder (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
  · exact fun u hu => (mrt_quadratic_remainder_hasDeriv hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (mrt_quadratic_remainder_hasDeriv (by simpa using hu)).hasDerivWithinAt
  · intro u hu
    exact mrt_quadratic_remainder_deriv_nonpos (by simpa using hu)

lemma mrt_quadratic_remainder_tendsto : Tendsto mrtQuadraticRemainder atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact mrt_quadratic_remainder_nonneg hu
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact mrt_quadratic_remainder_le_inv hu

/-- Finite Dirichlet summation with a nonnegative decreasing weight. -/
lemma mrt_antitone_weighted_prefix (a : ℕ → ℂ) (b : ℕ → ℝ) {Q : ℝ}
    (hQ : 0 ≤ Q) (hA : ∀ n, ‖∑ i ∈ range n, a i‖ ≤ Q)
    (hb : ∀ n, 0 ≤ b n) (hanti : Antitone b) (N : ℕ) :
    ‖∑ i ∈ range N, (b i : ℂ) * a i‖ ≤ Q * b 0 := by
  cases N with
  | zero => simpa using mul_nonneg hQ (hb 0)
  | succ N =>
    have he : (∑ i ∈ range (N + 1), (b i : ℂ) * a i) =
        (b N : ℂ) * (∑ i ∈ range (N + 1), a i) -
          ∑ i ∈ range N, ((b (i + 1) - b i : ℝ) : ℂ) * (∑ j ∈ range (i + 1), a j) := by
      simpa only [Nat.add_sub_cancel, Complex.real_smul] using
        (sum_range_by_parts b a (N + 1))
    rw [he]
    calc
      _ ≤ ‖(b N : ℂ) * (∑ i ∈ range (N + 1), a i)‖ +
          ‖∑ i ∈ range N, ((b (i + 1) - b i : ℝ) : ℂ) * (∑ j ∈ range (i + 1), a j)‖ :=
        norm_sub_le _ _
      _ ≤ b N * Q + ∑ i ∈ range N, (b i - b (i + 1)) * Q := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb N)]
          exact mul_le_mul_of_nonneg_left (hA (N + 1)) (hb N)
        · apply (norm_sum_le _ _).trans
          apply sum_le_sum
          intro i _
          have hi : b (i + 1) ≤ b i := hanti (Nat.le_succ i)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hi)]
          have hh := mul_le_mul_of_nonneg_left (hA (i + 1)) (sub_nonneg.mpr hi)
          simpa only [neg_sub] using hh
      _ = Q * b 0 := by rw [← sum_mul, sum_range_sub']; ring

lemma mrt_quadratic_remainder_weighted_prefix (a : ℕ → ℂ) {Q t : ℝ}
    (hQ : 0 ≤ Q) (ht : 0 < t) (hA : ∀ n, ‖∑ i ∈ range n, a i‖ ≤ Q) (N : ℕ) :
    ‖∑ i ∈ range N, (mrtQuadraticRemainder (t * (i + 1 : ℕ)) : ℂ) * a i‖ ≤ Q := by
  let b : ℕ → ℝ := fun i => mrtQuadraticRemainder (t * (i + 1 : ℕ))
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    exact mrt_quadratic_remainder_nonneg (mul_pos ht (by positivity))
  have hanti : Antitone b := by
    intro i j hij
    apply mrt_quadratic_remainder_antitone (mul_pos ht (by positivity))
      (mul_pos ht (by positivity))
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hij 1) ht.le
  exact (mrt_antitone_weighted_prefix a b hQ hA hb hanti N).trans
    (mul_le_of_le_one_right hQ (by simpa only [b, Nat.cast_zero, Nat.cast_add,
      Nat.cast_one, zero_add, mul_one] using
      mrt_quadratic_remainder_le_one ht))

end TwoPointCorrelations

end OAI

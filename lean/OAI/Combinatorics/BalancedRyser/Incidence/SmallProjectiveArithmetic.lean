import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

namespace OAI

namespace Balanced.SmallProjectiveArithmetic

theorem exists_interpolation_degree (δ : ℕ) (hδ : 0 < δ) :
    ∃ d : ℕ, d ^ 2 < 2 * δ ∧ 2 * δ < (d + 1) * (d + 2) := by
  let d := Nat.sqrt (2 * δ - 1)
  have hs : d ^ 2 ≤ 2 * δ - 1 := Nat.sqrt_le' _
  have ht : 2 * δ - 1 < (d + 1) * (d + 1) := Nat.lt_succ_sqrt _
  have hpred : 2 * δ - 1 + 1 = 2 * δ := by omega
  refine ⟨d, by omega, ?_⟩
  nlinarith

theorem three_degree_lt_order {q δ d : ℕ}
    (hsmall : (δ : ℝ) < (201 / 10000 : ℝ) * (q : ℝ) ^ 2)
    (hd : d ^ 2 < 2 * δ) : 3 * d < q := by
  have hdR : (d : ℝ) ^ 2 < 2 * (δ : ℝ) := by exact_mod_cast hd
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hs : (3 * (d : ℝ)) ^ 2 < (q : ℝ) ^ 2 := by nlinarith [sq_nonneg (q : ℝ)]
  have hlin : 3 * (d : ℝ) < q := by nlinarith
  exact_mod_cast hlin

theorem half_line_of_degree_bound {q d on : ℕ}
    (hd : 3 * d < q) (hon : q - d ≤ on) :
    q + 1 ≤ 2 * on := by
  omega

theorem tangent_total_gt_degree_threshold {q n δ d τ : ℕ}
    (hn : n ≤ q)
    (hsmall : (δ : ℝ) < (201 / 10000 : ℝ) * (q : ℝ) ^ 2)
    (hd : d ^ 2 < 2 * δ)
    (hcount : (q + 1) * (2 * q - n) ≤ 2 * δ + τ) :
    n * (d + 1) < τ := by
  have hdq := three_degree_lt_order hsmall hd
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hnq : (n : ℝ) ≤ q := by exact_mod_cast hn
  have hcountR : ((q : ℝ) + 1) * (2 * (q : ℝ) - n) ≤ 2 * (δ : ℝ) + τ := by
    have hs : n ≤ 2 * q := by omega
    exact_mod_cast hcount
  have hdqR : 3 * (d : ℝ) < q := by exact_mod_cast hdq
  have hprod := mul_lt_mul_of_pos_left hdqR hq
  have hsize := mul_nonneg (sub_nonneg.mpr hnq) (show (0 : ℝ) ≤ q + 1 by positivity)
  have htotal : (q : ℝ) * ((d : ℝ) + 1) < τ := by
    nlinarith [sq_nonneg (q : ℝ)]
  have hbound : (n : ℝ) * ((d : ℝ) + 1) ≤ (q : ℝ) * ((d : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hnq (by positivity)
  exact_mod_cast hbound.trans_lt htotal

theorem half_line_skew_refinement (q on off missing δ : ℕ)
    (hline : on + missing = q + 1)
    (hsize : off + on ≤ q)
    (hhalf : q + 1 ≤ 2 * on)
    (hcount : missing * (q - off) ≤ δ) :
    (q : ℝ) + 1 - 2 * (δ : ℝ) / ((q : ℝ) + 1) ≤ on := by
  have hon : on ≤ q - off := by omega
  have hcount' : missing * on ≤ δ := (Nat.mul_le_mul_left missing hon).trans hcount
  have hlineR : (on : ℝ) + missing = (q : ℝ) + 1 := by exact_mod_cast hline
  have hhalfR : (q : ℝ) + 1 ≤ 2 * (on : ℝ) := by exact_mod_cast hhalf
  have hcountR : (missing : ℝ) * on ≤ δ := by exact_mod_cast hcount'
  have hnonneg : (0 : ℝ) ≤ missing := Nat.cast_nonneg _
  have hpay : ((q : ℝ) + 1 - on) * ((q : ℝ) + 1) ≤ 2 * δ := by
    nlinarith
  have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hdiv : (q : ℝ) + 1 - on ≤ 2 * (δ : ℝ) / ((q : ℝ) + 1) :=
    (le_div_iff₀ hq).mpr hpay
  linarith

end Balanced.SmallProjectiveArithmetic

end OAI

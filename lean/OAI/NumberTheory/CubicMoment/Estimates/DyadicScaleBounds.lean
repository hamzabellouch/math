import OAI.NumberTheory.CubicMoment.Estimates.ModelPartialSummation
import Mathlib.Analysis.Normed.Group.Tannery

namespace OAI

/-! A summable majorant for first-moment scales along contracting dyads. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

def regularizedMomentScale (X : ℝ) : ℝ := X^(5/6:ℝ)/(1+Real.log X)

def dyadicMomentRatio (j : ℕ) : ℝ :=
  (1+(j:ℝ)*Real.log 2)*((2:ℝ)^(-(5/6:ℝ)))^j

lemma regularizedMomentScale_pos {X : ℝ} (hX : 1 ≤ X) :
    0 < regularizedMomentScale X := by
  unfold regularizedMomentScale
  exact div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) _)
    (by linarith [Real.log_nonneg hX])

lemma regularized_dyadic_scale {X : ℝ} (hX : 1 < X) (j : ℕ)
    (hY : 1 ≤ X/(2:ℝ)^j) :
    regularizedMomentScale (X/(2:ℝ)^j)/firstMomentScale X ≤ dyadicMomentRatio j := by
  have hXp : 0 < X := zero_lt_one.trans hX
  have hYp : 0 < X/(2:ℝ)^j := div_pos hXp (by positivity)
  have hYL : 0 ≤ Real.log (X/(2:ℝ)^j) := Real.log_nonneg hY
  have hL : 0 < 1+Real.log (X/(2:ℝ)^j) := by linarith
  have hpow : (X/(2:ℝ)^j)^(5/6:ℝ) = X^(5/6:ℝ)*((2:ℝ)^(-(5/6:ℝ)))^j := by
    rw [Real.div_rpow hXp.le (by positivity),←Real.rpow_pow_comm (by norm_num),
      Real.rpow_neg (by norm_num),inv_pow,div_eq_mul_inv]
  have hlog : Real.log X = Real.log (X/(2:ℝ)^j)+(j:ℝ)*Real.log 2 := by
    rw [Real.log_div hXp.ne' (by positivity),Real.log_pow]
    ring
  have hratio : Real.log X/(1+Real.log (X/(2:ℝ)^j)) ≤ 1+(j:ℝ)*Real.log 2 := by
    apply (div_le_iff₀ hL).mpr
    rw [hlog]
    nlinarith [mul_nonneg hYL (mul_nonneg (Nat.cast_nonneg j)
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))]
  calc
    _ = ((2:ℝ)^(-(5/6:ℝ)))^j *
        (Real.log X/(1+Real.log (X/(2:ℝ)^j))) := by
      unfold regularizedMomentScale firstMomentScale
      rw [hpow]
      field_simp
    _ ≤ ((2:ℝ)^(-(5/6:ℝ)))^j * (1+(j:ℝ)*Real.log 2) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by unfold dyadicMomentRatio; ring

lemma dyadicMomentRatio_summable : Summable dyadicMomentRatio := by
  let r := (2:ℝ)^(-(5/6:ℝ))
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgn : Summable (fun j : ℕ => (j:ℝ)*r^j) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
      (by simpa only [Real.norm_of_nonneg hr.le] using hr1)
  have hg : Summable (fun j : ℕ => r^j) := summable_geometric_of_lt_one hr.le hr1
  convert hg.add (hgn.mul_left (Real.log 2)) using 1
  ext j
  unfold dyadicMomentRatio
  dsimp [r]
  ring

lemma firstMomentScale_le_two_regularized {X : ℝ} (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    firstMomentScale X ≤ 2*regularizedMomentScale X := by
  have hL : 0 < Real.log X := zero_lt_one.trans_le hX
  have hL1 : 0 < 1+Real.log X := by linarith
  unfold firstMomentScale regularizedMomentScale
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ hL hL1).mpr
  nlinarith [Real.rpow_nonneg hXp.le (5/6:ℝ)]

lemma firstMomentScale_dyadic_isBigO (j : ℕ) :
    (fun X : ℝ => firstMomentScale (X/(2:ℝ)^j)) =O[atTop] firstMomentScale := by
  have ht : Tendsto (fun X : ℝ => X/(2:ℝ)^j) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  apply IsBigO.of_bound (2*dyadicMomentRatio j)
  filter_upwards [ht.eventually_ge_atTop (Real.exp 1),eventually_gt_atTop (1:ℝ)] with X hY hX
  have hY1 : 1 < X/(2:ℝ)^j := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)).trans_le hY
  have hYL : 1 ≤ Real.log (X/(2:ℝ)^j) := by
    have hh := Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
      (zero_lt_one.trans hY1) hY
    simpa only [Real.log_exp] using hh
  rw [Real.norm_of_nonneg (firstMomentScale_pos hY1).le,
    Real.norm_of_nonneg (firstMomentScale_pos hX).le]
  have hr := (div_le_iff₀ (firstMomentScale_pos hX)).mp
    (regularized_dyadic_scale hX j hY1.le)
  exact (firstMomentScale_le_two_regularized (zero_lt_one.trans hY1) hYL).trans (by linarith)

end CubicFirstMoment

end

end OAI

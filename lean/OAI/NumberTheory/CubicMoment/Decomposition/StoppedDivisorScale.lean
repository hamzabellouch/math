import OAI.NumberTheory.CubicMoment.Decomposition.StoppedFilteredCore

namespace OAI

/-! Elementary scaling of the unrestricted sieve on shortened rows. -/
noncomputable section
namespace CubicFirstMoment

lemma quotient_power_times_self {b q : ℝ} (hb : 0 < b) (hq : 0 < q) (a : ℝ) :
    (b/q)^a*(b/q) = b^(a+1)*q^(-(a+1)) := by
  calc
    _ = (b/q)^(a+1) := by rw [Real.rpow_add (div_pos hb hq),Real.rpow_one]
    _ = b^(a+1)/q^(a+1) := Real.div_rpow hb.le hq.le (a+1)
    _ = _ := by rw [Real.rpow_neg hq.le,div_eq_mul_inv]

lemma stopped_outer_row_scale {b q B : ℝ} (hb : 0 < b) (hq : 0 < q) (hB : 0 ≤ B) :
    (B+(B*(b/q))^(2/3:ℝ)+B^(1/3:ℝ)*(b/q))*(b/q) =
      B*b*q^(-1:ℝ)+B^(2/3:ℝ)*b^(5/3:ℝ)*q^(-5/3:ℝ)+
        B^(1/3:ℝ)*b^2*q^(-2:ℝ) := by
  have hmid : (B*(b/q))^(2/3:ℝ)*(b/q) =
      B^(2/3:ℝ)*b^(5/3:ℝ)*q^(-5/3:ℝ) := by
    rw [Real.mul_rpow hB (div_nonneg hb.le hq.le),mul_assoc,
      quotient_power_times_self hb hq]
    norm_num
    ring
  have hsq : (b/q)^2 = b^2*q^(-2:ℝ) := by
    rw [Real.rpow_neg hq.le,Real.rpow_two,div_pow,div_eq_mul_inv]
  have hone : B*(b/q) = B*b*q^(-1:ℝ) := by
    rw [Real.rpow_neg_one]
    ring
  calc
    _ = B*(b/q)+(B*(b/q))^(2/3:ℝ)*(b/q)+B^(1/3:ℝ)*(b/q)^2 := by ring
    _ = _ := by rw [hmid,hsq,hone]; ring

lemma stopped_outer_row_scale_le {b q B ε : ℝ} (hb : 0 < b) (hq : 1 ≤ q)
    (hB : 0 ≤ B) (hε : 0 ≤ ε) :
    (2*B*(b/q))^ε*(B+(B*(b/q))^(2/3:ℝ)+B^(1/3:ℝ)*(b/q))*(b/q) ≤
      (2*B*b)^ε*(B*b*q^(-1:ℝ)+B^(2/3:ℝ)*b^(5/3:ℝ)*q^(-5/3:ℝ)+
        B^(1/3:ℝ)*b^2*q^(-2:ℝ)) := by
  have hqp : 0 < q := zero_lt_one.trans_le hq
  have hquot : b/q ≤ b := (div_le_iff₀ hqp).mpr (by nlinarith)
  calc
    _ = (2*B*(b/q))^ε*((B+(B*(b/q))^(2/3:ℝ)+B^(1/3:ℝ)*(b/q))*(b/q)) := by ring
    _ ≤ (2*B*b)^ε*((B+(B*(b/q))^(2/3:ℝ)+B^(1/3:ℝ)*(b/q))*(b/q)) := by
      apply mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left hquot (by positivity)) hε)
      positivity
    _ = _ := by rw [stopped_outer_row_scale hb hqp hB]

end CubicFirstMoment

end

end OAI

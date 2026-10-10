import OAI.Analysis.LipschitzHilbert.Estimates.TopWeight
import OAI.Analysis.LipschitzHilbert.Estimates.BoxVariationWeights
import OAI.Analysis.LipschitzHilbert.Packets.PacketBoxes

namespace OAI

/-! Convert the lattice decay in the global concentration estimate into
the eighth power of the manuscript's actual slope-box weight. -/

noncomputable section
namespace LipschitzHilbert

theorem floor_abs_bound (x : ℝ) : |x| ≤ |((⌊x⌋:ℤ):ℝ)|+1 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  exact abs_le.mpr ⟨by linarith [neg_abs_le (⌊x⌋:ℝ)],
    by linarith [le_abs_self (⌊x⌋:ℝ)]⟩

theorem boxVariationWeight_floor_bound (x y : ℝ) :
    (1+|x|+|y|)*boxVariationWeight (⌊x⌋,⌊y⌋) ≤ 5 := by
  let i : ℝ := ⌊x⌋
  let j : ℝ := ⌊y⌋
  have hi : |i| ≤ 1+i^2 := by nlinarith [sq_nonneg (|i|-1), sq_abs i]
  have hj : |j| ≤ 1+j^2 := by nlinarith [sq_nonneg (|j|-1), sq_abs j]
  have hbase : 1+|x|+|y| ≤ 5*((1+i^2)*(1+j^2)) := by
    have hx := floor_abs_bound x
    have hy := floor_abs_bound y
    change |x| ≤ |i|+1 at hx
    change |y| ≤ |j|+1 at hy
    nlinarith [sq_nonneg i, sq_nonneg j, mul_nonneg (sq_nonneg i) (sq_nonneg j)]
  have hden : 0 < (1+i^2)*(1+j^2) := by positivity
  have heq : boxVariationWeight (⌊x⌋,⌊y⌋) = ((1+i^2)*(1+j^2))⁻¹ := by
    simp [boxVariationWeight, lineEnvelope, i, j, mul_comm]
  rw [heq, ← div_eq_mul_inv]
  exact (div_le_iff₀ hden).mpr hbase

theorem boxVariationWeight_floor_power (x y : ℝ) (m : ℕ) :
    boxVariationWeight (⌊x⌋,⌊y⌋)^m ≤ 5^m/(1+|x|+|y|)^m := by
  have hb : 0 < 1+|x|+|y| := by positivity
  apply (le_div_iff₀ (pow_pos hb m)).mpr
  have hp := pow_le_pow_left₀
    (mul_nonneg (by positivity) (boxVariationWeight_pos (⌊x⌋,⌊y⌋)).le)
    (boxVariationWeight_floor_bound x y) m
  simpa only [mul_pow, mul_comm] using hp

namespace SlopeBox

theorem weight_nat_eighth (T : SlopeBox) (K : ℝ) (hK : 0 < K) (d : ℕ) (z : ℝ × ℝ) :
    (T.weight K (d:ℝ) z)^8 = (2:ℝ)^(8*d)/(1+T.radius z/K)^(8*d) := by
  have hb : 0 ≤ 1+T.radius z/K := by
    have := T.radius_nonnegative z
    positivity
  simp only [weight, Real.rpow_neg hb, Real.rpow_natCast, mul_pow, inv_pow, ← pow_mul]
  rw [mul_comm d 8]
  simp only [div_eq_mul_inv]

theorem lattice_decay_le_weight (T : SlopeBox) (K : ℝ) (hK : 0 < K)
    (d : ℕ) (z : ℝ × ℝ) :
    boxVariationWeight (packetBoxIndex T.x (T.y-T.slope*T.x)
      (K*T.length) (K*T.width) z.1 (z.2-T.slope*z.1))^(8*d) ≤
        (5:ℝ)^(8*d)*(T.weight K (d:ℝ) z)^8 := by
  let X := (z.1-T.x)/(K*T.length)
  let Y := ((z.2-T.slope*z.1)-(T.y-T.slope*T.x))/(K*T.width)
  have hr : 1+|X|+|Y| = 1+T.radius z/K := by
    unfold radius horizontal transverse
    dsimp [X,Y]
    rw [abs_div, abs_div, abs_of_pos (mul_pos hK T.length_pos),
      abs_of_pos (mul_pos hK T.width_pos), abs_div, abs_div,
      abs_of_pos T.length_pos, abs_of_pos T.width_pos]
    have heq : (z.2-T.slope*z.1)-(T.y-T.slope*T.x) =
        (z.2-T.y)-T.slope*(z.1-T.x) := by ring
    rw [heq]
    ring
  have hp := boxVariationWeight_floor_power X Y (8*d)
  change boxVariationWeight (⌊X⌋,⌊Y⌋)^(8*d) ≤ _
  apply hp.trans
  rw [hr, T.weight_nat_eighth K hK]
  have hden : 0 < (1+T.radius z/K)^(8*d) := by
    have := T.radius_nonnegative z
    positivity
  have htwo : (1:ℝ) ≤ 2^(8*d) := one_le_pow₀ (by norm_num)
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hden.le
  exact le_mul_of_one_le_right (by positivity) htwo

end SlopeBox
end LipschitzHilbert

end

end OAI

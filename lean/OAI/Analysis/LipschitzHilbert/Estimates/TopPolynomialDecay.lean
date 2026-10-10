import OAI.Analysis.LipschitzHilbert.Estimates.TopLatticeDecay
import OAI.Analysis.LipschitzHilbert.Packets.PolynomialPacket

namespace OAI

/-! The inverse of the fixed polynomial top weight is bounded by the
eighth power of the physical slope-box weight. -/

noncomputable section
namespace LipschitzHilbert.SlopeBox

theorem inverse_polynomial_le_weight (T : SlopeBox) (K : ℝ) (hK : 0 < K)
    (D : ℕ) (z : ℝ × ℝ) :
    (polynomialWeight T.x (K*T.length) (8*D+1) z.1 *
      polynomialWeight (T.y-T.slope*T.x) (K*T.width) (8*D+1) (z.2-T.slope*z.1))⁻¹ ≤
        (T.weight K (D:ℝ) z)^8 := by
  let X := (z.1-T.x)/(K*T.length)
  let Y := ((z.2-T.slope*z.1)-(T.y-T.slope*T.x))/(K*T.width)
  let B := (1+X^2)*(1+Y^2)
  have hB : 1 ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg X,sq_nonneg Y,mul_nonneg (sq_nonneg X) (sq_nonneg Y)]
  have hsum : 1+|X|+|Y| ≤ 2*B := by
    have hx : 2*|X| ≤ 1+X^2 := by nlinarith [sq_nonneg (|X|-1),sq_abs X]
    have hy : 2*|Y| ≤ 1+Y^2 := by nlinarith [sq_nonneg (|Y|-1),sq_abs Y]
    dsimp [B]
    nlinarith [sq_nonneg X,sq_nonneg Y,mul_nonneg (sq_nonneg X) (sq_nonneg Y)]
  have hr : 1+T.radius z/K = 1+|X|+|Y| := by
    symm
    unfold radius horizontal transverse
    dsimp [X,Y]
    rw [abs_div,abs_div,abs_of_pos (mul_pos hK T.length_pos),
      abs_of_pos (mul_pos hK T.width_pos),abs_div,abs_div,
      abs_of_pos T.length_pos,abs_of_pos T.width_pos]
    have heq : (z.2-T.slope*z.1)-(T.y-T.slope*T.x) =
        (z.2-T.y)-T.slope*(z.1-T.x) := by ring
    rw [heq]
    ring
  have hpoly : polynomialWeight T.x (K*T.length) (8*D+1) z.1 *
      polynomialWeight (T.y-T.slope*T.x) (K*T.width) (8*D+1) (z.2-T.slope*z.1) =
        B^(8*D+1) := by
    simp only [polynomialWeight,← mul_pow]
    simp only [B,X,Y,div_pow]
  rw [hpoly,T.weight_nat_eighth K hK,hr]
  have hden : 0 < (1+|X|+|Y|)^(8*D) := by positivity
  have hpow : (1+|X|+|Y|)^(8*D) ≤ 2^(8*D)*B^(8*D+1) := by
    calc
      _ ≤ (2*B)^(8*D) := pow_le_pow_left₀ (by positivity) hsum _
      _ = 2^(8*D)*B^(8*D) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hB (Nat.le_add_right _ _)) (by positivity)
  apply (le_div_iff₀ hden).mpr
  have hd := (div_le_iff₀ (pow_pos (zero_lt_one.trans_le hB) (8*D+1))).mpr hpow
  simpa only [div_eq_mul_inv,mul_comm] using hd

end LipschitzHilbert.SlopeBox

end

end OAI

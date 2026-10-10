import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFunction

namespace OAI

/-! The geometric inversion in the cubic theta transformation, restricted
only by positive height and nonzero level. No automorphy law is assumed. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRadius (p : ℂ × ℝ) : ℝ := Complex.normSq p.1+p.2^2

def cubicThetaInversion (q : ℂ) (p : ℂ × ℝ) : ℂ × ℝ :=
  (-star p.1/(q^2*(cubicThetaRadius p:ℂ)),
    p.2/(Complex.normSq q*cubicThetaRadius p))

lemma cubicThetaRadius_pos {p : ℂ × ℝ} (hp : 0 < p.2) : 0 < cubicThetaRadius p := by
  unfold cubicThetaRadius
  exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hp)

lemma cubicThetaInversion_height_pos {q : ℂ} (hq : q ≠ 0) {p : ℂ × ℝ} (hp : 0 < p.2) :
    0 < (cubicThetaInversion q p).2 :=
  div_pos hp (mul_pos (Complex.normSq_pos.mpr hq) (cubicThetaRadius_pos hp))

lemma cubicThetaInversion_center (q : ℂ) {v : ℝ} (hv : 0 < v) :
    cubicThetaInversion q (0,v) = (0,(Complex.normSq q*v)⁻¹) := by
  apply Prod.ext
  · simp [cubicThetaInversion]
  · dsimp [cubicThetaInversion,cubicThetaRadius]
    simp only [map_zero,zero_add]
    by_cases hq : q = 0
    · simp [hq]
    · have hN : Complex.normSq q ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hq)
      field_simp

lemma cubicThetaInversion_radius {q : ℂ} (hq : q ≠ 0) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaRadius (cubicThetaInversion q p) =
      (Complex.normSq q^2*cubicThetaRadius p)⁻¹ := by
  have hρ := cubicThetaRadius_pos hp
  have hN := Complex.normSq_pos.mpr hq
  unfold cubicThetaRadius cubicThetaInversion
  simp only [Complex.normSq_div,Complex.normSq_neg,Complex.star_def,Complex.normSq_conj,
    Complex.normSq_mul,map_pow,Complex.normSq_ofReal,div_pow]
  dsimp only [cubicThetaRadius] at hρ ⊢
  field_simp

end CubicFirstMoment

end

end OAI

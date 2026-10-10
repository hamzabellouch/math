import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionGeometry

namespace OAI

/-! The level-scaled hyperbolic inversion is an involution. This fixes
its conjugations and powers before using it in a transformation formula. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaInversion_involutive {q : ℂ} (hq : q ≠ 0)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaInversion q (cubicThetaInversion q p) = p := by
  have hρ := cubicThetaRadius_pos hp
  have hN := Complex.normSq_pos.mpr hq
  have hρC : (cubicThetaRadius p:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have hNC : (Complex.normSq q:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hqstar : star q ≠ 0 := star_ne_zero.mpr hq
  have hprod : (Complex.normSq q:ℂ) = q*star q := by
    exact (Complex.mul_conj q).symm
  have hrad := cubicThetaInversion_radius hq hp
  apply Prod.ext
  · change -star (-star p.1/(q^2*(cubicThetaRadius p:ℂ)))/
        (q^2*(cubicThetaRadius (cubicThetaInversion q p):ℂ)) = p.1
    rw [hrad]
    simp only [Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.star_def,map_neg,map_div₀,map_mul,map_pow,Complex.conj_conj,Complex.conj_ofReal,
      neg_div,neg_neg]
    change p.1/((star q)^2*(cubicThetaRadius p:ℂ))/
      (q^2*((Complex.normSq q:ℂ)^2*(cubicThetaRadius p:ℂ))⁻¹) = p.1
    rw [hprod]
    field_simp
  · change (p.2/(Complex.normSq q*cubicThetaRadius p))/
        (Complex.normSq q*cubicThetaRadius (cubicThetaInversion q p)) = p.2
    rw [hrad]
    field_simp

end CubicFirstMoment

end

end OAI

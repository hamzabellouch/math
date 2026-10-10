import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusAction

namespace OAI

/-! Translation and level inversion matrices in the exact coordinates
used by the cubic theta Fourier and Mellin expansions. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaTranslationMatrix (t : ℂ) : SL(2,ℂ) :=
  ⟨!![1,t;0,1],by simp [Matrix.det_fin_two]⟩

def cubicThetaInversionMatrix (q : ℂ) (hq : q ≠ 0) : SL(2,ℂ) :=
  ⟨!![0,-q⁻¹;q,0],by simp [Matrix.det_fin_two,hq]⟩

lemma cubicThetaMobius_translation (t : ℂ) (p : ℂ × ℝ) :
    cubicThetaMobius (cubicThetaTranslationMatrix t) p = (p.1+t,p.2) := by
  apply Prod.ext <;>
    simp [cubicThetaMobius,cubicThetaTranslationMatrix,
      cubicThetaMobiusDenominator,cubicThetaMobiusNumerator]

lemma cubicThetaInversionMatrix_denominator {q : ℂ} (hq : q ≠ 0) (p : ℂ × ℝ) :
    cubicThetaMobiusDenominator (cubicThetaInversionMatrix q hq) p =
      Complex.normSq q*cubicThetaRadius p := by
  simp [cubicThetaMobiusDenominator,cubicThetaInversionMatrix,cubicThetaRadius,
    Complex.normSq_mul,mul_add]

theorem cubicThetaMobius_inversion {q : ℂ} (hq : q ≠ 0)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaMobius (cubicThetaInversionMatrix q hq) p = cubicThetaInversion q p := by
  have hstar : star q ≠ 0 := star_ne_zero.mpr hq
  have hρ : (cubicThetaRadius p:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (cubicThetaRadius_pos hp)
  have hN : (Complex.normSq q:ℂ) = q*star q := (Complex.mul_conj q).symm
  apply Prod.ext
  · change cubicThetaMobiusNumerator (cubicThetaInversionMatrix q hq) p/
      (cubicThetaMobiusDenominator (cubicThetaInversionMatrix q hq) p:ℂ) = _
    rw [cubicThetaInversionMatrix_denominator]
    simp only [cubicThetaMobiusNumerator,cubicThetaInversionMatrix,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,zero_mul,zero_add,
      add_zero,star_mul,Complex.ofReal_mul,hN,cubicThetaInversion]
    change (-q⁻¹*(star p.1*star q))/(q*star q*(cubicThetaRadius p:ℂ)) =
      -star p.1/(q^2*(cubicThetaRadius p:ℂ))
    field_simp
  · change p.2/cubicThetaMobiusDenominator (cubicThetaInversionMatrix q hq) p =
      p.2/(Complex.normSq q*cubicThetaRadius p)
    rw [cubicThetaInversionMatrix_denominator]

end CubicFirstMoment

end

end OAI

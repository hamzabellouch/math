import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusGeometry

namespace OAI

/-! Hermitian coordinates for the actual hyperbolic action. They give
the composition law without any analytic or automorphy assumption. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaHermitian (p : ℂ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(cubicThetaRadius p:ℂ),p.1;star p.1,1]

def cubicThetaMobiusQuadratic (g : SL(2,ℂ)) (p : ℂ × ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (g : Matrix (Fin 2) (Fin 2) ℂ)*cubicThetaHermitian p*
    (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ

lemma cubicThetaMobiusQuadratic_entries (g : SL(2,ℂ)) (p : ℂ × ℝ) :
    cubicThetaMobiusQuadratic g p =
      !![((Complex.normSq (g 0 0*p.1+g 0 1)+Complex.normSq (g 0 0)*p.2^2:ℝ):ℂ),
          cubicThetaMobiusNumerator g p;
          star (cubicThetaMobiusNumerator g p),(cubicThetaMobiusDenominator g p:ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [cubicThetaMobiusQuadratic,cubicThetaHermitian,cubicThetaRadius,
      cubicThetaMobiusNumerator,cubicThetaMobiusDenominator,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.conjTranspose_apply,Matrix.of_apply,
      Complex.ofReal_add,Complex.ofReal_mul,Complex.normSq_eq_conj_mul_self,
      map_add,map_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_conj] <;> dsimp <;> ring

lemma cubicThetaHermitian_mobius (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaHermitian (cubicThetaMobius g p) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹ • cubicThetaMobiusQuadratic g p := by
  have hD : (cubicThetaMobiusDenominator g p:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (cubicThetaMobius_denominator_pos g hp)
  rw [cubicThetaMobiusQuadratic_entries]
  ext i j
  fin_cases i <;> fin_cases j
  · change (cubicThetaRadius (cubicThetaMobius g p):ℂ) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹ *
        ((Complex.normSq (g 0 0*p.1+g 0 1)+Complex.normSq (g 0 0)*p.2^2:ℝ):ℂ)
    rw [cubicThetaMobius_radius g hp,Complex.ofReal_div]
    ring
  · change cubicThetaMobiusNumerator g p/(cubicThetaMobiusDenominator g p:ℂ) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹*cubicThetaMobiusNumerator g p
    ring
  · change star (cubicThetaMobiusNumerator g p/(cubicThetaMobiusDenominator g p:ℂ)) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹*star (cubicThetaMobiusNumerator g p)
    simp only [map_div₀,Complex.star_def,Complex.conj_ofReal]
    ring
  · change (1:ℂ) = (cubicThetaMobiusDenominator g p:ℂ)⁻¹*(cubicThetaMobiusDenominator g p:ℂ)
    exact (inv_mul_cancel₀ hD).symm

lemma cubicThetaMobiusQuadratic_comp (g h : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaMobiusQuadratic h (cubicThetaMobius g p) =
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹ • cubicThetaMobiusQuadratic (h*g) p := by
  rw [cubicThetaMobiusQuadratic,cubicThetaHermitian_mobius g hp]
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  simp only [cubicThetaMobiusQuadratic,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.conjTranspose_mul,Matrix.mul_assoc]

end CubicFirstMoment

end

end OAI

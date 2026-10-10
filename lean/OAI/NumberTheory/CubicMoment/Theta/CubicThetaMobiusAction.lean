import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusMatrix

namespace OAI

/-! Composition and positive-height action for the hyperbolic matrices
used in the cubic theta transformation. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaMobiusDenominator_comp (g h : SL(2,ℂ))
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaMobiusDenominator h (cubicThetaMobius g p) =
      cubicThetaMobiusDenominator (h*g) p/cubicThetaMobiusDenominator g p := by
  have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1)
    (cubicThetaMobiusQuadratic_comp g h hp)
  simp only [cubicThetaMobiusQuadratic_entries,Matrix.of_apply,Matrix.cons_val_one,Matrix.cons_val_zero,
    Matrix.smul_apply,smul_eq_mul] at hm
  have he : (cubicThetaMobiusDenominator h (cubicThetaMobius g p):ℂ) =
      (cubicThetaMobiusDenominator (h*g) p:ℂ)/(cubicThetaMobiusDenominator g p:ℂ) := by
    rw [hm]
    ring
  exact_mod_cast he

lemma cubicThetaHermitian_comp (g h : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaHermitian (cubicThetaMobius h (cubicThetaMobius g p)) =
      cubicThetaHermitian (cubicThetaMobius (h*g) p) := by
  have hD : (cubicThetaMobiusDenominator g p:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (cubicThetaMobius_denominator_pos g hp)
  have hD' : (cubicThetaMobiusDenominator (h*g) p:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (cubicThetaMobius_denominator_pos (h*g) hp)
  rw [cubicThetaHermitian_mobius h (cubicThetaMobius_height_pos g hp),
    cubicThetaMobiusQuadratic_comp g h hp,cubicThetaHermitian_mobius (h*g) hp,smul_smul,
    cubicThetaMobiusDenominator_comp g h hp,Complex.ofReal_div]
  congr 1
  field_simp

theorem cubicThetaMobius_comp (g h : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0 < p.2) :
    cubicThetaMobius h (cubicThetaMobius g p) = cubicThetaMobius (h*g) p := by
  apply Prod.ext
  · have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1)
      (cubicThetaHermitian_comp g h hp)
    simpa only [cubicThetaHermitian,Matrix.cons_val_zero,Matrix.of_apply,Matrix.cons_val_one] using hm
  · change (p.2/cubicThetaMobiusDenominator g p)/
      cubicThetaMobiusDenominator h (cubicThetaMobius g p) =
        p.2/cubicThetaMobiusDenominator (h*g) p
    rw [cubicThetaMobiusDenominator_comp g h hp]
    have hD := ne_of_gt (cubicThetaMobius_denominator_pos g hp)
    have hD' := ne_of_gt (cubicThetaMobius_denominator_pos (h*g) hp)
    field_simp

@[simp] lemma cubicThetaMobius_one (p : ℂ × ℝ) : cubicThetaMobius 1 p = p := by
  apply Prod.ext <;>
    simp [cubicThetaMobius,cubicThetaMobiusNumerator,cubicThetaMobiusDenominator]

/-- Hyperbolic three-space in the coordinates of the manuscript. -/
def CubicThetaPoint := {p : ℂ × ℝ // 0 < p.2}

instance : MulAction SL(2,ℂ) CubicThetaPoint where
  smul g p := ⟨cubicThetaMobius g p.val,cubicThetaMobius_height_pos g p.property⟩
  one_smul p := Subtype.ext (cubicThetaMobius_one p.val)
  mul_smul g h p := Subtype.ext (cubicThetaMobius_comp h g p.property).symm

end CubicFirstMoment

end

end OAI

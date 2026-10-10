import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusContinuity

namespace OAI

/-! An explicit determinant-one frame carrying (0,1) to any positive-height
point. It transports fixed-point calculations to the unit Hermitian form. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPointFrame (p : CubicThetaPoint) : SL(2,ℂ) :=
  ⟨!![(Real.sqrt p.val.2:ℂ),p.val.1/(Real.sqrt p.val.2:ℂ);0,1/(Real.sqrt p.val.2:ℂ)],by
    rw [Matrix.det_fin_two_of]
    have hs : (Real.sqrt p.val.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p.property).ne'
    field_simp
    ring⟩

lemma cubicThetaPointFrame_denominator (p : CubicThetaPoint) :
    cubicThetaMobiusDenominator (cubicThetaPointFrame p) (0,1)=1/p.val.2 := by
  simp only [cubicThetaMobiusDenominator,cubicThetaPointFrame,Matrix.of_apply,
    Matrix.cons_val_one,Matrix.cons_val_zero,zero_mul,zero_add,Complex.normSq_div,
    Complex.normSq_one,Complex.normSq_ofReal,one_pow,Complex.normSq_zero,mul_one,add_zero]
  rw [Real.mul_self_sqrt p.property.le]

lemma cubicThetaPointFrame_numerator (p : CubicThetaPoint) :
    cubicThetaMobiusNumerator (cubicThetaPointFrame p) (0,1)=p.val.1/(p.val.2:ℂ) := by
  have hs : (Real.sqrt p.val.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p.property).ne'
  have hv : (Real.sqrt p.val.2:ℂ)^2=(p.val.2:ℂ) := by exact_mod_cast Real.sq_sqrt p.property.le
  simp only [cubicThetaMobiusNumerator,cubicThetaPointFrame,Matrix.of_apply,
    Matrix.cons_val_one,Matrix.cons_val_zero,zero_mul,zero_add,star_zero,mul_zero,add_zero,
    one_pow,map_div₀,Complex.star_def,Complex.conj_ofReal,map_one]
  rw [← hv]
  field_simp

lemma cubicThetaPointFrame_base (p : CubicThetaPoint) :
    cubicThetaMobius (cubicThetaPointFrame p) (0,1)=p.val := by
  apply Prod.ext
  · change cubicThetaMobiusNumerator (cubicThetaPointFrame p) (0,1)/
        (cubicThetaMobiusDenominator (cubicThetaPointFrame p) (0,1):ℂ)=p.val.1
    rw [cubicThetaPointFrame_numerator,cubicThetaPointFrame_denominator,Complex.ofReal_div,Complex.ofReal_one]
    field_simp [Complex.ofReal_ne_zero.mpr p.property.ne']
  · change 1/cubicThetaMobiusDenominator (cubicThetaPointFrame p) (0,1)=p.val.2
    rw [cubicThetaPointFrame_denominator]
    field_simp [p.property.ne']

lemma cubicThetaPointFrame_inverse (p : CubicThetaPoint) :
    cubicThetaMobius (cubicThetaPointFrame p)⁻¹ p.val=(0,1) := by
  rw [← cubicThetaPointFrame_base p,cubicThetaMobius_comp _ _ (by norm_num)]
  simp

lemma cubicThetaPointFrame_conjugate_fixed (p : CubicThetaPoint) (g : SL(2,ℂ))
    (hg : cubicThetaMobius g p.val=p.val) :
    cubicThetaMobius ((cubicThetaPointFrame p)⁻¹*g*cubicThetaPointFrame p) (0,1)=(0,1) := by
  rw [← cubicThetaMobius_comp _ _ (by norm_num),cubicThetaPointFrame_base,
    ← cubicThetaMobius_comp g (cubicThetaPointFrame p)⁻¹ p.property,hg,cubicThetaPointFrame_inverse]

end CubicFirstMoment

end

end OAI

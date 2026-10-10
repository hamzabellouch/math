import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusMatrix

namespace OAI

/-! Determinant-one Hermitian coordinates and the invariant two-point
quantity underlying the hyperbolic metric. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaUnitHermitian (p : ℂ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (p.2:ℂ)⁻¹ • cubicThetaHermitian p

lemma cubicThetaUnitHermitian_mobius (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaUnitHermitian (cubicThetaMobius g p)=
      g.val*cubicThetaUnitHermitian p*g.valᴴ := by
  have hv : (p.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hd : (cubicThetaMobiusDenominator g p:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaMobius_denominator_pos g hp).ne'
  rw [cubicThetaUnitHermitian,cubicThetaHermitian_mobius g hp]
  change ((p.2/cubicThetaMobiusDenominator g p:ℝ):ℂ)⁻¹ •
    ((cubicThetaMobiusDenominator g p:ℂ)⁻¹ • cubicThetaMobiusQuadratic g p)=_
  rw [Complex.ofReal_div,smul_smul]
  have hs : ((p.2:ℂ)/(cubicThetaMobiusDenominator g p:ℂ))⁻¹*
      (cubicThetaMobiusDenominator g p:ℂ)⁻¹=(p.2:ℂ)⁻¹ := by field_simp
  rw [hs]
  simp only [cubicThetaUnitHermitian,cubicThetaMobiusQuadratic,Matrix.mul_smul,Matrix.smul_mul]

lemma cubicThetaUnitHermitian_pair_det_invariant (g : SL(2,ℂ))
    {p q : ℂ × ℝ} (hp : 0<p.2) (hq : 0<q.2) :
    Matrix.det (cubicThetaUnitHermitian (cubicThetaMobius g p)+
      cubicThetaUnitHermitian (cubicThetaMobius g q))=
    Matrix.det (cubicThetaUnitHermitian p+cubicThetaUnitHermitian q) := by
  rw [cubicThetaUnitHermitian_mobius g hp,cubicThetaUnitHermitian_mobius g hq,
    ← Matrix.add_mul,← Matrix.mul_add,Matrix.det_mul,Matrix.det_mul,
    Matrix.det_conjTranspose,g.property]
  simp

lemma cubicThetaUnitHermitian_pair_det {p q : ℂ × ℝ} (hp : 0<p.2) (hq : 0<q.2) :
    Matrix.det (cubicThetaUnitHermitian p+cubicThetaUnitHermitian q)=
      (4:ℂ)+((Complex.normSq (p.1-q.1)+(p.2-q.2)^2)/(p.2*q.2):ℝ) := by
  have hv : (p.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hw : (q.2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hq.ne'
  simp only [cubicThetaUnitHermitian,cubicThetaHermitian,cubicThetaRadius,
    Matrix.det_fin_two,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_sub,
    Complex.normSq_eq_conj_mul_self,map_sub,Complex.star_def]
  field_simp
  ring

def cubicThetaHyperbolicChord (p q : ℂ × ℝ) : ℝ :=
  (Complex.normSq (p.1-q.1)+(p.2-q.2)^2)/(p.2*q.2)

lemma cubicThetaHyperbolicChord_invariant (g : SL(2,ℂ))
    {p q : ℂ × ℝ} (hp : 0<p.2) (hq : 0<q.2) :
    cubicThetaHyperbolicChord (cubicThetaMobius g p) (cubicThetaMobius g q)=
      cubicThetaHyperbolicChord p q := by
  have h := cubicThetaUnitHermitian_pair_det_invariant g hp hq
  rw [cubicThetaUnitHermitian_pair_det (cubicThetaMobius_height_pos g hp)
    (cubicThetaMobius_height_pos g hq),cubicThetaUnitHermitian_pair_det hp hq] at h
  apply Complex.ofReal_injective
  exact add_left_cancel h

end CubicFirstMoment

end

end OAI

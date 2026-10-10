import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedRows

namespace OAI

/-! Primitive rows at the translated inverted cusps used by the primary
coefficient projector. The phase is kept as the actual cubic symbol; its
ramified evaluation is a subsequent arithmetic step. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicTheta_primary_add_three_mul {c d : Eisenstein} (hc : primary c)
    (hd : (3:Eisenstein)∣d) (b : Eisenstein) : primary (c+b*d) := by
  obtain ⟨t,ht⟩ := hc
  obtain ⟨u,hu⟩ := hd
  refine ⟨t+b*u,?_⟩
  linear_combination ht+b*hu

def cubicThetaShiftedInvertedRowEquiv (b : Eisenstein) :
    CubicThetaBottomRow ≃ CubicThetaInvertedRow where
  toFun r := {
    c := r.d+b*r.c
    d := -r.c
    c_primary := cubicTheta_primary_add_three_mul r.d_primary r.c_three b
    d_three := dvd_neg.mpr r.c_three
    coprime := by
      obtain ⟨u,v,h⟩ := r.coprime
      refine ⟨v,v*b-u,?_⟩
      linear_combination h }
  invFun r := {
    c := -r.d
    d := r.c+b*r.d
    c_three := dvd_neg.mpr r.d_three
    d_primary := cubicTheta_primary_add_three_mul r.c_primary r.d_three b
    coprime := by
      obtain ⟨u,v,h⟩ := r.coprime
      refine ⟨u*b-v,u,?_⟩
      linear_combination h }
  left_inv r := by ext <;> dsimp <;> ring
  right_inv r := by ext <;> dsimp <;> ring

def cubicThetaShiftedInversion (b : Eisenstein) : SL(2,Eisenstein) :=
  ⟨!![b,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma cubicThetaShiftedInversion_complex (b : Eisenstein) :
    cubicThetaFullComplex (cubicThetaShiftedInversion b) =
      cubicThetaTranslationMatrix (b:ℂ)*cubicThetaInversionMatrix 1 one_ne_zero := by
  have he : cubicThetaShiftedInversion b = cubicThetaFullTranslation b*cubicThetaFullInversion := by
    apply Subtype.ext
    change (!![b,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)=!![1,b;0,1]*!![0,-1;1,0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two]
  rw [he,map_mul,cubicThetaFullTranslation_complex,cubicThetaFullInversion_complex]

lemma cubicThetaMobius_shiftedInversion (b : Eisenstein) {p : ℂ×ℝ} (hp : 0<p.2) :
    cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p =
      ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) := by
  rw [cubicThetaShiftedInversion_complex,←cubicThetaMobius_comp _ _ hp,
    cubicThetaMobius_translation,cubicThetaMobius_inversion one_ne_zero hp]

lemma cubicThetaBottomRow_height_shiftedInverted (r : CubicThetaBottomRow)
    (b : Eisenstein) {p : ℂ×ℝ} (hp : 0<p.2) :
    r.height (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p) =
      (cubicThetaShiftedInvertedRowEquiv b r).height p := by
  rw [cubicThetaBottomRow_height_full r _ hp]
  simp only [cubicThetaShiftedInversion,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_zero,mul_one,mul_neg_one,add_zero]
  change p.2/(Complex.normSq ((((r.c*b+r.d:Eisenstein):ℂ)*p.1+(-r.c:Eisenstein)))+
    norm (r.c*b+r.d)*p.2^2)=_
  have he : r.c*b+r.d=r.d+b*r.c := by ring
  rw [he]
  rfl

def cubicThetaShiftedInvertedTerm (b : Eisenstein) (r : CubicThetaInvertedRow)
    (p : ℂ×ℝ) (s : ℂ) : ℂ :=
  cubicSymbol (r.c+b*r.d) r.d*(r.height p:ℂ)^s

theorem cubicThetaEisenstein_shiftedInverted {p : ℂ×ℝ} (hp : 0<p.2)
    (b : Eisenstein) (s : ℂ) :
    cubicThetaEisenstein ((cubicThetaInversion 1 p).1+b,(cubicThetaInversion 1 p).2) s =
      ∑' r : CubicThetaInvertedRow, cubicThetaShiftedInvertedTerm b r p s := by
  rw [←cubicThetaMobius_shiftedInversion b hp]
  unfold cubicThetaEisenstein
  have he (r : CubicThetaBottomRow) :
      cubicThetaEisensteinTerm r
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p) s =
      cubicThetaShiftedInvertedTerm b (cubicThetaShiftedInvertedRowEquiv b r) p s := by
    rw [cubicThetaEisensteinTerm,CubicThetaBottomRow.phase,star_star,
      cubicThetaBottomRow_height_shiftedInverted r b hp]
    dsimp only [cubicThetaShiftedInvertedTerm,cubicThetaShiftedInvertedRowEquiv,Equiv.coe_fn_mk]
    have hx : r.d+b*r.c+b*(-r.c)=r.d := by ring
    rw [hx,cubicSymbol_neg r.d_primary]
  simp_rw [he]
  exact (cubicThetaShiftedInvertedRowEquiv b).tsum_eq
    (fun r => cubicThetaShiftedInvertedTerm b r p s)

end CubicFirstMoment

end

end OAI

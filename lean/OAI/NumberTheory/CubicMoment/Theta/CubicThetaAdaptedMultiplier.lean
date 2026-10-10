import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedMultiplier

namespace OAI

/-! A principal-level decomposition evaluates the common multiplier for
cusp lifts with both diagonal entries zero modulo three. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaFullTranslation_neg (a : Eisenstein) :
    cubicThetaFullTranslation (-a)=(cubicThetaFullTranslation a)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [←cubicThetaFullTranslation_add,neg_add_cancel]
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

lemma cubicThetaRightInversion_matrix (g : SL(2,Eisenstein)) :
    (g*cubicThetaFullInversion⁻¹).val=!![-g 0 1,g 0 0;-g 1 1,g 1 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv]
  change g.val*Matrix.adjugate !![(0:Eisenstein),-1;1,0]=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

lemma cubicThetaRightInversion_mem (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) :
    g*cubicThetaFullInversion⁻¹∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hb : primary (-g 0 1) := by
    change (3:Eisenstein)∣-g 0 1-1
    rw [show -g 0 1-1= -g 0 0*g 1 1+g 0 1*(g 1 0-1) by linear_combination hdet]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_neg.mpr ha) _)
      (dvd_mul_of_dvd_right hc _)
  rw [show (g*cubicThetaFullInversion⁻¹).val= _ from cubicThetaRightInversion_matrix g]
  exact ⟨hb,ha,dvd_neg.mpr hd,hc⟩

def cubicThetaRightInversionPrincipal (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) : cubicThetaPrincipalGroup :=
  ⟨g*cubicThetaFullInversion⁻¹,cubicThetaRightInversion_mem g hc ha hd⟩

lemma cubicThetaRightInversion_value (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) :
    cubicThetaKubotaValue (cubicThetaRightInversionPrincipal g hc ha hd)=
      cubicSymbol (g 1 0) (g 0 0) := by
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubota_column_switch]
  change cubicSymbol ((g*cubicThetaFullInversion⁻¹).val 1 1)
    ((g*cubicThetaFullInversion⁻¹).val 0 1)=_
  rw [cubicThetaRightInversion_matrix]
  rfl

theorem cubicThetaPrimaryBottom_multiplier_adapted (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0) (hd : (3:Eisenstein)∣g 1 1) :
    cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)=
      cubicSymbol (g 1 0) (g 0 0) := by
  obtain ⟨a,ha'⟩ := ha
  obtain ⟨d,hd'⟩ := hd
  let h := cubicThetaRightInversionPrincipal g hc ⟨a,ha'⟩ ⟨d,hd'⟩
  let k := cubicThetaKubotaConjugate cubicThetaModularS (cubicThetaPrincipalTranslation (-d))
  let l := cubicThetaPrincipalTranslation (-a)
  have he : cubicThetaPrimaryBottomPrincipal g hc=h*k*l := by
    apply Subtype.ext
    change g*(cubicThetaPrimaryBottomSeed g)⁻¹=
      (g*cubicThetaFullInversion⁻¹)*
        (cubicThetaModularS*(cubicThetaPrincipalTranslation (-d)).val*cubicThetaModularS⁻¹)*
          (cubicThetaPrincipalTranslation (-a)).val
    have hS : cubicThetaModularS=cubicThetaFullInversion := rfl
    have htd : (cubicThetaPrincipalTranslation (-d)).val=
        (cubicThetaFullTranslation (3*d))⁻¹ := by
      change cubicThetaFullTranslation (3*(-d))=_
      rw [mul_neg,cubicThetaFullTranslation_neg]
    have hta : (cubicThetaPrincipalTranslation (-a)).val=
        (cubicThetaFullTranslation (3*a))⁻¹ := by
      change cubicThetaFullTranslation (3*(-a))=_
      rw [mul_neg,cubicThetaFullTranslation_neg]
    rw [cubicThetaPrimaryBottomSeed,cubicThetaShiftedInversion_factor,ha',hd',hS,htd,hta]
    group
  rw [he,cubicThetaKubotaValue_mul,cubicThetaKubotaValue_mul]
  have hk : cubicThetaKubotaValue k=1 := by
    rw [show k=cubicThetaKubotaConjugate cubicThetaModularS (cubicThetaPrincipalTranslation (-d)) from rfl,
      cubicThetaKubotaValue_conjugate_S,cubicThetaPrincipalTranslation_value]
  rw [hk,show cubicThetaKubotaValue l=1 from cubicThetaPrincipalTranslation_value _,mul_one,mul_one]
  exact cubicThetaRightInversion_value g hc _ _

end CubicFirstMoment

end

end OAI

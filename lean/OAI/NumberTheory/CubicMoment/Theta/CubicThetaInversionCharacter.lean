import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedRows
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTranslatedCuspStrip
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAutomorphicSections

namespace OAI

/-! Inversion preserves the actual cubic multiplier. Consequently its
pullback acts on genuine automorphic sections, with no new multiplier input. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaInversionConjugate_entries (g : cubicThetaPrincipalGroup) :
    (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g).val 0 0=g.val 1 1 ∧
    (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g).val 1 0= -g.val 0 1 := by
  have hi : (cubicThetaFullInversion⁻¹:SL(2,Eisenstein)).val=!![0,1;-1,0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    change Matrix.adjugate !![(0:Eisenstein),-1;1,0]=_
    simp [Matrix.adjugate_fin_two]
  change ((cubicThetaFullInversion⁻¹)⁻¹*g.val*cubicThetaFullInversion⁻¹) 0 0=g.val 1 1 ∧
    ((cubicThetaFullInversion⁻¹)⁻¹*g.val*cubicThetaFullInversion⁻¹) 1 0= -g.val 0 1
  rw [inv_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul,hi]
  simp [cubicThetaFullInversion,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma cubicThetaInversionConjugate_character (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g)=
      cubicThetaKubotaValue g := by
  obtain ⟨h00,h10⟩ := cubicThetaInversionConjugate_entries g
  rw [cubicThetaKubotaValue_eq_symbol,h00,h10,
    cubicSymbol_neg (cubicThetaPrincipalGroup_diagonal_primary g).2,
    ←cubicThetaKubota_column_switch g,←cubicThetaKubotaValue_eq_symbol]

lemma cubicThetaInversion_intertwine (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaFullInversion • (g • p)=
      cubicThetaPrincipalConjugate cubicThetaFullInversion⁻¹ g •
        (cubicThetaFullInversion • p) := by
  change cubicThetaFullInversion • (g.val • p)=
    ((cubicThetaFullInversion⁻¹)⁻¹*g.val*cubicThetaFullInversion⁻¹) • (cubicThetaFullInversion • p)
  rw [inv_inv]
  simp only [←mul_smul,mul_assoc,inv_mul_cancel,mul_one]

def cubicThetaInversionSection (F : CubicThetaSection) : CubicThetaSection :=
  ⟨⟨fun p => F.val (cubicThetaFullInversion • p),
    F.val.continuous.comp (continuous_const_smul cubicThetaFullInversion)⟩,by
      intro g p
      change F.val (cubicThetaFullInversion • (g • p))=
        cubicThetaKubotaValue g*F.val (cubicThetaFullInversion • p)
      rw [cubicThetaInversion_intertwine,F.property,cubicThetaInversionConjugate_character]⟩

lemma cubicThetaInversionSection_apply (F : CubicThetaSection) (p : CubicThetaPoint) :
    (cubicThetaInversionSection F).val p=F.val (cubicThetaFullInversion • p) := rfl

def cubicThetaInversionSectionLinear : CubicThetaSection →ₗ[ℂ] CubicThetaSection where
  toFun := cubicThetaInversionSection
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExtendedAutomorphy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedInvertedRows

namespace OAI

/-! A full integral matrix with primary lower-left entry reduces to an
actual translated inversion through a principal-level matrix. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaPrimaryBottomSeed (g : SL(2,Eisenstein)) : SL(2,Eisenstein) :=
  cubicThetaShiftedInversion (g 0 0)*cubicThetaFullTranslation (g 1 1)

def cubicThetaPrimaryBottomDefect (g : SL(2,Eisenstein)) : SL(2,Eisenstein) :=
  g*(cubicThetaPrimaryBottomSeed g)⁻¹

lemma cubicThetaPrimaryBottomSeed_matrix (g : SL(2,Eisenstein)) :
    (cubicThetaPrimaryBottomSeed g).val=!![g 0 0,g 0 0*g 1 1-1;1,g 1 1] := by
  change (!![g 0 0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)*!![1,g 1 1;0,1]=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,sub_eq_add_neg]

lemma cubicThetaPrimaryBottomDefect_matrix (g : SL(2,Eisenstein)) :
    (cubicThetaPrimaryBottomDefect g).val=
      !![1+g 0 1*(g 1 0-1),-g 0 0*g 0 1*(g 1 0-1);
        g 1 1*(g 1 0-1),1+(1-g 0 0*g 1 1)*(g 1 0-1)] := by
  have hg : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  rw [cubicThetaPrimaryBottomDefect,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv,cubicThetaPrimaryBottomSeed_matrix]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.adjugate_fin_two]
  all_goals dsimp
  · change g 0 0*g 1 1+g 0 1*(-1)=1+g 0 1*(g 1 0-1)
    linear_combination hg
  · change g 0 0*(-(g 0 0*g 1 1-1))+g 0 1*g 0 0= -g 0 0*g 0 1*(g 1 0-1)
    linear_combination -g 0 0*hg
  · change g 1 0*g 1 1+g 1 1*(-1)=g 1 1*(g 1 0-1)
    ring
  · change g 1 0*(-(g 0 0*g 1 1-1))+g 1 1*g 0 0=1+(1-g 0 0*g 1 1)*(g 1 0-1)
    ring

lemma cubicThetaPrimaryBottomDefect_mem (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) :
    cubicThetaPrimaryBottomDefect g∈cubicThetaPrincipalGroup := by
  apply (cubicThetaPrincipalGroup_mem_iff _).mpr
  have he := cubicThetaPrimaryBottomDefect_matrix g
  change primary ((cubicThetaPrimaryBottomDefect g).val 0 0) ∧
    (3:Eisenstein)∣(cubicThetaPrimaryBottomDefect g).val 0 1 ∧
    (3:Eisenstein)∣(cubicThetaPrimaryBottomDefect g).val 1 0 ∧
    primary ((cubicThetaPrimaryBottomDefect g).val 1 1)
  rw [he]
  change (3:Eisenstein)∣(1+g 0 1*(g 1 0-1))-1 ∧
    (3:Eisenstein)∣-g 0 0*g 0 1*(g 1 0-1) ∧
    (3:Eisenstein)∣g 1 1*(g 1 0-1) ∧
    (3:Eisenstein)∣(1+(1-g 0 0*g 1 1)*(g 1 0-1))-1
  obtain ⟨t,ht⟩ := hc
  refine ⟨⟨g 0 1*t,?_⟩,⟨-g 0 0*g 0 1*t,?_⟩,⟨g 1 1*t,?_⟩,
    ⟨(1-g 0 0*g 1 1)*t,?_⟩⟩ <;> rw [ht] <;> ring

def cubicThetaPrimaryBottomPrincipal (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) :
    cubicThetaPrincipalGroup := ⟨cubicThetaPrimaryBottomDefect g,cubicThetaPrimaryBottomDefect_mem g hc⟩

theorem cubicThetaNormalizedSeries_primaryBottom (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (g • p)=
      cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)*
        cubicThetaNormalizedSeriesSection.val
          (cubicThetaShiftedInversion (g 0 0) • (cubicThetaFullTranslation (g 1 1) • p)) := by
  have hg : g=(cubicThetaPrimaryBottomPrincipal g hc).val*cubicThetaPrimaryBottomSeed g := by
    change g=(g*(cubicThetaPrimaryBottomSeed g)⁻¹)*cubicThetaPrimaryBottomSeed g
    simp
  calc
    _ = cubicThetaNormalizedSeriesSection.val
        (cubicThetaPrimaryBottomPrincipal g hc • (cubicThetaPrimaryBottomSeed g • p)) := by
      change cubicThetaNormalizedSeriesSection.val (g • p)=
        cubicThetaNormalizedSeriesSection.val
          ((cubicThetaPrimaryBottomPrincipal g hc).val • (cubicThetaPrimaryBottomSeed g • p))
      rw [←mul_smul]
      exact congrArg (fun u : SL(2,Eisenstein) => cubicThetaNormalizedSeriesSection.val (u • p)) hg
    _ = cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)*
        cubicThetaNormalizedSeriesSection.val (cubicThetaPrimaryBottomSeed g • p) :=
      cubicThetaNormalizedSeriesSection.property _ _
    _ = _ := by rw [cubicThetaPrimaryBottomSeed,mul_smul]

end CubicFirstMoment

end

end OAI

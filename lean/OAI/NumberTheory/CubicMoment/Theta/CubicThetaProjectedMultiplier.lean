import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedCoefficient

namespace OAI

/-! The actual three cusp multipliers agree when the lower-right entry is
zero modulo three. This is the elementary supplementary-law step needed
before finite Ramanujan summation. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimaryBottom_multiplier_symbol (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)=
      cubicSymbol (1+g 0 1*(g 1 0-1)) (g 1 1*(g 1 0-1)) := by
  rw [cubicThetaKubotaValue_eq_symbol]
  change cubicSymbol ((cubicThetaPrimaryBottomDefect g).val 0 0)
    ((cubicThetaPrimaryBottomDefect g).val 1 0)=_
  rw [cubicThetaPrimaryBottomDefect_matrix]
  rfl

lemma cubicThetaProjectedCuspMatrix_entries (g : SL(2,Eisenstein)) (j : Fin 3) :
    cubicThetaProjectedCuspMatrix g j 0 1=g 0 1+(j.val:Eisenstein)*omegaE*g 1 1 ∧
    cubicThetaProjectedCuspMatrix g j 1 0=g 1 0 ∧
    cubicThetaProjectedCuspMatrix g j 1 1=g 1 1 := by
  change ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 0 1=_ ∧
    ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 0=_ ∧
    ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 1=_
  simp [Matrix.mul_apply,Fin.sum_univ_two]

theorem cubicThetaProjectedCuspMultiplier_constant (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (hd : (3:Eisenstein)∣g 1 1) (j : Fin 3) :
    cubicThetaProjectedCuspMultiplier g hc j=
      cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc) := by
  have hj := cubicThetaProjectedCuspMatrix_entries g j
  have hpj := (cubicThetaPrincipalGroup_diagonal_primary
    (cubicThetaPrimaryBottomPrincipal (cubicThetaProjectedCuspMatrix g j)
      (cubicThetaProjectedCuspMatrix_primary g hc j))).1
  have hp := (cubicThetaPrincipalGroup_diagonal_primary (cubicThetaPrimaryBottomPrincipal g hc)).1
  change primary ((cubicThetaPrimaryBottomDefect (cubicThetaProjectedCuspMatrix g j)).val 0 0) at hpj
  change primary ((cubicThetaPrimaryBottomDefect g).val 0 0) at hp
  rw [cubicThetaPrimaryBottomDefect_matrix] at hpj hp
  change primary (1+cubicThetaProjectedCuspMatrix g j 0 1*
    (cubicThetaProjectedCuspMatrix g j 1 0-1)) at hpj
  change primary (1+g 0 1*(g 1 0-1)) at hp
  rw [hj.1,hj.2.1] at hpj
  unfold cubicThetaProjectedCuspMultiplier
  rw [cubicThetaPrimaryBottom_multiplier_symbol,cubicThetaPrimaryBottom_multiplier_symbol,
    hj.1,hj.2.1,hj.2.2]
  apply cubicSymbol_periodic_of_nine_and_numerator hpj hp
  · obtain ⟨d,hd⟩ := hd
    obtain ⟨c,hc⟩ := hc
    refine ⟨(j.val:Eisenstein)*omegaE*d*c,?_⟩
    rw [hd,hc]
    ring
  · refine ⟨(j.val:Eisenstein)*omegaE,?_⟩
    ring

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridEquation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeightEquation

namespace OAI

/-! Every literal Eisenstein grid summand satisfies the same spectral
equation, including the distinguished cusp row and the zero extension. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinGridTerm_zero (d : Eisenstein) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinGridTerm (0,d) p s=if d=1 then (p.2:ℂ)^s else 0 := by
  by_cases hd : d=1
  · subst d
    simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,primary_one,
      cubicSymbol_one_lower,norm,isCoprime_zero_left]
  · have hp : ¬(primary d ∧ IsCoprime (0:Eisenstein) d) := by
      intro h
      exact hd (primary_unit_eq_one (isCoprime_zero_left.mp h.2) h.1)
    simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hd,hp]

theorem cubicThetaEisensteinGrid_eigenvalue (c d : Eisenstein) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint x y v) s := by
  by_cases hc0 : c=0
  · subst c
    simp only [cubicThetaEisensteinGridTerm_zero,cubicThetaCartesianPoint]
    by_cases hd : d=1
    · simp only [ite_eq_left hd]
      exact cubicThetaHyperbolicOperator_height s x y hv
    · simp only [ite_eq_right hd,cubicThetaHyperbolicOperator,deriv_const',deriv_const,
        mul_zero,sub_zero,add_zero]
  · by_cases hc : (3:Eisenstein)∣c
    · exact cubicThetaEisensteinGridTerm_eigenvalue hc hc0 d s x y hv
    · have he : (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s)=
          (fun _ _ _ => (0:ℂ)) := by
        funext a b t
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc]
      rw [he]
      simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc,
        cubicThetaHyperbolicOperator]

end CubicFirstMoment

end

end OAI

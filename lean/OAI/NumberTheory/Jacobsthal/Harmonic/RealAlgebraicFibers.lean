import OAI.NumberTheory.Jacobsthal.Estimates.DivisibleInflection
import OAI.NumberTheory.Jacobsthal.Probability.MarkedStripTotal

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection ErdosLocalFiberGraphs

theorem finite_real_preimage (A : Set ℂ) (hA : A.Finite) :
    (Complex.ofReal ⁻¹' A).Finite ∧ (Complex.ofReal ⁻¹' A).ncard ≤ A.ncard := by
  refine ⟨hA.preimage Complex.ofReal_injective.injOn,?_⟩
  exact ncard_le_ncard_of_injOn Complex.ofReal (fun _ h => h) Complex.ofReal_injective.injOn hA

theorem real_vertical_nonzero (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (x : ℝ) : verticalPolynomial Q x ≠ 0 := by
  intro hz
  have hdegC : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  let P := ErdosBivariateResultant.specialize (nestedY ℂ (complexify Q)) (x : ℂ)
  have hp : P ≠ 0 := nonlinear_fibers_nonzero (complexify Q) hQ hdegC x
  have hroot : ∀ y : ℝ, P.IsRoot (y : ℂ) := by
    intro y
    have hy : peval Q x y = 0 := by rw [← verticalPolynomial_eval,hz,Polynomial.eval_zero]
    change ErdosBivariateResultant.beval (nestedY ℂ (complexify Q)) (x : ℂ) (y : ℂ) = 0
    rw [beval_nested,complexify_eval,← peval_eq_eval_pair,hy,Complex.ofReal_zero]
  have hinf : (range Complex.ofReal).Infinite := infinite_range_of_injective Complex.ofReal_injective
  apply hinf
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  rintro y ⟨z,rfl⟩
  exact hroot z

end ErdosAlgebraicCurve

end

end Erdos970

end OAI

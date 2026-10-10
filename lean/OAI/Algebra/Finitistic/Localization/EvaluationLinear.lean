import OAI.Algebra.Finitistic.Localization.QuotientActionEvaluation

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
open BalancedTensor FiniteProjectiveHomotopy
universe u v w z
namespace BalancedTensor
variable (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

instance tensorFunctorLinear : (tensorFunctor.{u,v,w,z} k A N).Linear k where
  map_smul {M M'} f c := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.ext
    intro m n
    exact LinearMap.congr_fun ((mk k A (ScalarModule k A M') N).map_smul c (f.hom m)) n

instance homotopyEvaluationLinear : (homotopyEvaluation.{u,v,w,z} k A N).Linear k :=
  inferInstanceAs (((tensorFunctor.{u,v,w,z} k A N).mapHomotopyCategory (.up ℤ)).Linear k)
end BalancedTensor
namespace QuadraticEncoding
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

instance boundedEvaluationLinear : (boundedEvaluation X).Linear k :=
  inferInstanceAs ((inclusion (B P)ᵐᵒᵖ ⋙ homotopyEvaluation k (B P) X.Evaluation).Linear k)

instance boundedQuotientEvaluationLinear : (boundedQuotientEvaluation X).Linear k :=
  (Localization.functor_linear_iff (boundedDenominators P).Q (boundedDenominators P) k
    (boundedEvaluation X) (boundedQuotientEvaluation X)).mp inferInstance
end QuadraticEncoding
end LittleFinitistic

end

end OAI

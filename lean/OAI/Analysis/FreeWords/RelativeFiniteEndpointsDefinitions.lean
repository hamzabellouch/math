import Mathlib
import OAI.Analysis.FreeWords.AmplifiedModelDefinitions
import OAI.Analysis.FreeWords.RelativeEndpointLimitsDefinitions

namespace OAI

noncomputable section

namespace KKRelativeEndpoints

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def RelativeFiniteEndpoints : Prop :=
  ∀(M:VonNeumannAlgebra H) (τ:FaithfulNormalTrace M),IsFactor M → IsDiffuse M →
  ∀n:ℕ,∀F:Finset (List (MatrixAlgebra n M×MatrixAlgebra n M)),
  ∀E:Finset (List (MatrixAlgebra n M×MatrixAlgebra n M)×MatrixAlgebra n M),
    (∀w∈F,w≠[] ∧ ∀z∈w,∀a b,τ.map (z.1 a b)=0 ∧ τ.map (z.2 a b)=0) →
    (∀v∈E,(∀z∈v.1,∀a b,τ.map (z.1 a b)=0 ∧ τ.map (z.2 a b)=0) ∧
      ∀a b,τ.map (v.2 a b)=0) → ∀ε:ℝ,0<ε →
    ∃u:unitary (ConcreteAlgebra M),
      (∀w∈F,∀a b,‖τ.map (relativePair u w a b)‖<ε) ∧
      (∀v∈E,∀a b,‖τ.map ((relativePair u v.1*KKControlledConjugation.amplifyConj n u v.2) a b)‖<ε)

end

end KKRelativeEndpoints
end

end OAI

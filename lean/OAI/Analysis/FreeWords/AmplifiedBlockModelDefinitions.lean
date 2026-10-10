import Mathlib
import OAI.Analysis.FreeWords.AmplifiedModelDefinitions
import OAI.Analysis.FreeWords.HaarEndpointsDefinitions

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer KKMatrixExpectation KKHaarEndpoints

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def FiniteAmplifiedBlockModel : Prop :=
  ∀(M:VonNeumannAlgebra H) (τ:FaithfulNormalTrace M),IsFactor M → IsDiffuse M →
  ∀n:ℕ,0<n → ∀(K:Finset ℤ) (F:Finset (List (ℤ×MatrixAlgebra n M)))
    (E:Finset (List (ℤ×MatrixAlgebra n M)×ℤ)),
    (∀w∈F,w≠[] ∧ CenteredPowerWord (matrixTraceMap τ.map n) (numericalHom n).range.toSubalgebra w) →
    (∀z∈E,CenteredPowerWord (matrixTraceMap τ.map n) (numericalHom n).range.toSubalgebra z.1 ∧ z.2≠0) →
    ∀ε:ℝ,0<ε → ∃d:ℕ,0<d ∧
      ∃ρ:Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
      Function.Injective ρ ∧ ∃U:unitary (MatrixAlgebra n M),
        (∀i j,U.val i j∈ρ.range) ∧
        (∀k∈K,k≠0 → ‖matrixTrace τ n (U^k).val‖<ε) ∧
        (∀w∈F,‖matrixTrace τ n (powerWord U w)‖<ε) ∧
        (∀z∈E,∀a b,‖τ.map ((powerWord U z.1*(U^z.2).val) a b)‖<ε)

end

end KKFreeLiftFrontier
end

end OAI

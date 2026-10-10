import Mathlib
import OAI.Analysis.FreeWords.TransportBlocks

namespace OAI

noncomputable section

namespace KKFiniteTransport

noncomputable section

open KKTraceTransfer KKFreeLiftFrontier KKMatrixExpectation KKControlledConjugation

variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M:VonNeumannAlgebra H}

abbrev RelWord (τ:FaithfulNormalTrace M) (n:ℕ) := List (Block τ n×
  {x:MatrixAlgebra n M // matrixExpectation τ.map n x=0})

inductive TransportTest (τ:FaithfulNormalTrace M) (n:ℕ) where
  | haar (k:ℤ) (hk:k≠0)
  | block (b:Block τ n) (i j:Fin n)
  | cyclic (w:RelWord τ n) (hne:w≠[]) (i j:Fin n)
  | endpoint (w:RelWord τ n) (b:Block τ n) (i j:Fin n)

def transportPair (τ:FaithfulNormalTrace M) {n:ℕ} (U:unitary (MatrixAlgebra n M)) (w:RelWord τ n) :=
  (w.map fun z => blockCenter τ U z.1*z.2.val).prod

def modelWord (τ:FaithfulNormalTrace M) {n:ℕ} (U:unitary (MatrixAlgebra n M)) (w:RelWord τ n) :=
  w.map fun z => (blockCenter τ U z.1,z.2.val)

def testValue (τ:FaithfulNormalTrace M) {n:ℕ} (t:TransportTest τ n) (U:unitary (MatrixAlgebra n M)) : ℂ :=
  match t with
  | .haar k _ => matrixTraceMap τ.map n (U^k).val
  | .block b i j => τ.map (blockValue U b i j)
  | .cyclic w _ i j => τ.map (transportPair τ U w i j)
  | .endpoint w b i j => τ.map ((transportPair τ U w*blockCenter τ U b) i j)

def FiniteTransportTests : Prop :=
  ∀(M:VonNeumannAlgebra H) (τ:FaithfulNormalTrace M),IsFactor M → IsDiffuse M →
  ∀n:ℕ,0<n → ∀L:Finset (TransportTest τ n),∀ε:ℝ,0<ε →
    ∃U:unitary (MatrixAlgebra n M),FullMatrixUnitary n U ∧ ∀t∈L,‖testValue τ t U‖<ε

end

end KKFiniteTransport
end

end OAI

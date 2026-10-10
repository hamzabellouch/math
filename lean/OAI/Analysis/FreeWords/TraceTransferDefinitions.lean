import Mathlib
import OAI.Analysis.FreeWords.WeakCompact

namespace OAI

noncomputable section

open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction

namespace UniversalStrongKK

section OperatorMean

variable {G H : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (m : ScalarMean G)

variable [CompleteSpace H]

end OperatorMean

end UniversalStrongKK

open scoped Topology

namespace UniversalStrongKK

section UltraMean

variable {I : Type*} [TopologicalSpace I]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end UltraMean

end UniversalStrongKK

namespace UniversalStrongKK

open scoped InnerProductSpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end UniversalStrongKK

namespace KKTraceTransfer

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev WeakAlgebra (M : VonNeumannAlgebra H) :=
  {T : H →WOT[ℂ] H // T.toCLM ∈ M}

abbrev ConcreteAlgebra (M : VonNeumannAlgebra H) := ↥M.toStarSubalgebra

noncomputable def weakToAlgebra {M : VonNeumannAlgebra H} (T : WeakAlgebra M) : ConcreteAlgebra M :=
  ⟨T.val.toCLM, T.property⟩

structure FaithfulNormalTrace (M : VonNeumannAlgebra H) where
  map : ConcreteAlgebra M →ₗ[ℂ] ℂ
  positive : ∀ x : ConcreteAlgebra M, (x : H →L[ℂ] H).IsPositive → 0 ≤ map x
  normalized : map 1 = 1
  tracial : ∀ x y : ConcreteAlgebra M, map (x * y) = map (y * x)
  faithful : ∀ x : ConcreteAlgebra M, (x : H →L[ℂ] H).IsPositive → map x = 0 → x = 0
  normal : ∀ r : ℝ, ContinuousOn (fun T : WeakAlgebra M => map (weakToAlgebra T))
    {T | ‖T.val.toCLM‖ ≤ r}

def traceNorm {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (x : ConcreteAlgebra M) : ℝ :=
  Real.sqrt (τ.map (star x * x)).re

end

end KKTraceTransfer
end

end OAI

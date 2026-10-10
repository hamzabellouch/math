import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral

namespace OAI

/-! Continuous circle weights with invariant-projection and spectral properties. -/

namespace Invariant233

def Rotation.IsContinuousCounterexample (θ : ℝ) (f : C(Circle, ℝ)) : Prop :=
  IsContinuousCircleWeight f ∧
    let operator : Rotation.Hilbert →L[ℂ] Rotation.Hilbert := Rotation.weightedReal θ f
    let factor : VonNeumannAlgebra Rotation.Hilbert := Rotation.algebra θ
    operator ∈ factor ∧
    HasOnlyTrivialInvariantProjections (H := Rotation.Hilbert) factor operator ∧
    operator ≠ 0 ∧
    NormQuasinilpotent (A := Rotation.Hilbert →L[ℂ] Rotation.Hilbert) operator ∧
    vectorFugledeKadisonDeterminant (H := Rotation.Hilbert) Rotation.vacuum operator = 0

end Invariant233

end OAI

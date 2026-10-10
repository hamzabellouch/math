import OAI.Analysis.IrrationalRotation.Model.Spectral
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Model.GeneratedVonNeumann

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorFugledeKadisonDeterminant (ξ : H) (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
    (Real.exp ((vectorTrace ξ (CFC.log (star T * T + ε.val • (1 : H →L[ℂ] H)))).re / 2))

def IsVectorBrownMeasure (ξ : H) (T : H →L[ℂ] H) (μ : Measure ℂ) : Prop :=
  IsProbabilityMeasure μ ∧ IsCompact μ.support ∧ ∀ z : ℂ,
    vectorFugledeKadisonDeterminant ξ (T - z • (1 : H →L[ℂ] H)) =
      logarithmicPotentialDeterminant μ z

def operatorModulus (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (star T * T)

def HasCountablyAtomicSpectralType (B : H →L[ℂ] H) : Prop :=
  ∃ S : Set ℂ, S.Countable ∧
    (⨆ z : S, Module.End.eigenspace B.toLinearMap z.val).topologicalClosure = ⊤

def polarConjugate (U B : H →L[ℂ] H) (n : ℤ) : H →L[ℂ] H :=
  if 0 ≤ n then U ^ n.toNat * B * star U ^ n.toNat
  else star U ^ (-n).toNat * B * U ^ (-n).toNat

def finitePolarAlgebra (U B : H →L[ℂ] H) (F : Finset ℤ) : VonNeumannAlgebra H :=
  vonNeumannGenerated {A | ∃ n ∈ F, A = polarConjugate U B n}

def fullPolarAlgebra (U B : H →L[ℂ] H) : VonNeumannAlgebra H :=
  vonNeumannGenerated (Set.range (polarConjugate U B))

def ProductPolarStructure (U T : H →L[ℂ] H) : Prop :=
  star U * U = 1 ∧ U * star U = 1 ∧ T = U * operatorModulus T ∧
    Function.Injective (operatorModulus T) ∧ HasCountablyAtomicSpectralType (operatorModulus T) ∧
    (∀ F : Finset ℤ,
      IsAbelianVonNeumannAlgebra (finitePolarAlgebra U (operatorModulus T) F) ∧
      IsAtomicVonNeumannAlgebra (finitePolarAlgebra U (operatorModulus T) F)) ∧
    IsAbelianVonNeumannAlgebra (fullPolarAlgebra U (operatorModulus T)) ∧
    IsDiffuseVonNeumannAlgebra (fullPolarAlgebra U (operatorModulus T))

end Invariant233

end

end OAI

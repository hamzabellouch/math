import OAI.Analysis.KadisonSimilarity.Tracial.SourceConstantMoments
import OAI.Analysis.KadisonSimilarity.FreeProduct.ConstantConjugateFreeness

namespace OAI

/-! The conjugating unitary belongs to the prescribed source ultrapower. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance conjugateSourceAmbientClosed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance conjugateSourceClosed : IsClosed (R.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (R : Set (H →L[ℂ] H))
  infer_instance

include hfactor hdiff hirr in
/-- The required specialization of Popa's conjugacy theorem for a concrete
irreducible diffuse factor inclusion, with arbitrary smaller source algebra. -/
theorem popa1995_concrete_inclusion
    [TopologicalSpace.SeparableSpace (vectorPositiveFunctional M υ.vector).GNS]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    {D : Type*} [CStarAlgebra D] (ρ : D →⋆ₐ[ℂ] R.toStarSubalgebra) :
    Popa1995ConjugateFreenessInput (vectorPositiveFunctional R υ.vector)
      (vectorPositiveFunctional M υ.vector) (restrictedTrace υ hRM).trace_one υ.trace_one
      ω (restrictedTrace υ hRM).trace_mul_comm υ.trace_mul_comm
      (coordinateInclusion hRM) (fun _ => rfl) hω ρ := by
  obtain ⟨u, hu⟩ := exists_source_constant_integer_moments υ hRM hfactor hdiff hirr
    ω (hω.trans_eq Nat.cofinite_eq_atTop)
  exact popaConjugateFreeness_of_constant_moments (vectorPositiveFunctional R υ.vector)
    (vectorPositiveFunctional M υ.vector) (restrictedTrace υ hRM).trace_one υ.trace_one
    ω (restrictedTrace υ hRM).trace_mul_comm υ.trace_mul_comm
    (coordinateInclusion hRM) (fun _ => rfl) hω ρ u hu

end KadisonSimilarity

end

end OAI

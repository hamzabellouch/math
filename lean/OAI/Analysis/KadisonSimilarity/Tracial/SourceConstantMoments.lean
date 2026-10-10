import OAI.Analysis.KadisonSimilarity.Tracial.SourceAllMoments
import OAI.Analysis.KadisonSimilarity.Tracial.ConstantMomentLimit

namespace OAI

/-! Prescribed-source unitaries annihilate all centered constant mixed moments. -/

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

local instance constantMomentAmbientClosed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance constantMomentSourceClosed : IsClosed (R.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (R : Set (H →L[ℂ] H))
  infer_instance

include hfactor hdiff hirr in
theorem exists_source_constant_integer_moments
    [TopologicalSpace.SeparableSpace (vectorPositiveFunctional M υ.vector).GNS]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop) :
    ∃ u : ℕ → unitary R.toStarSubalgebra,
      ConstantIntegerMoments (B := M.toStarSubalgebra)
        (vectorPositiveFunctional M υ.vector) υ.trace_one ω υ.trace_mul_comm
        (fun n => mapUnitary (coordinateInclusion hRM) (u n)) := by
  let τ := vectorPositiveFunctional M υ.vector
  obtain ⟨d, hd, hdense⟩ := exists_trace_dense_contractions τ
  obtain ⟨u, hu⟩ := exists_source_quotient_unitary_all_moments υ hRM hfactor hdiff hirr ω hω
    (fun i => BoundedContinuousFunction.const ℕ (d i)) (fun i _ => hd i)
  exact ⟨u, constantIntegerMoments_of_dense τ υ.trace_one ω υ.trace_mul_comm
    d hd hdense (fun n => mapUnitary (coordinateInclusion hRM) (u n)) hu⟩

end KadisonSimilarity

end

end OAI

import OAI.Analysis.KadisonSimilarity.Tracial.SourceMomentSequence
import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerHom
import OAI.Analysis.KadisonSimilarity.Tracial.QuotientMomentLimit

namespace OAI

/-! Vanishing ultrapower moments produced by a sequence of source unitaries. -/

noncomputable section
namespace KadisonSimilarity

open Generator Generator.Tracial
open UltrapowerBridge (TracialRepresentation)
open HochschildComparison HochschildPatching HochschildUltrapower BoundedHochschild
open TracialUltrapower Filter Topology
open scoped ComplexOrder BoundedContinuousFunction

lemma source_map_asPartialUnitary {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (u : unitary A) :
    SourcePartialUnitary.map φ (asPartialUnitary u) = asPartialUnitary (mapUnitary φ u) := by
  apply HochschildComparison.PartialUnitary.ext
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {R M : VonNeumannAlgebra H} (υ : TracialRepresentation M) (hRM : R ≤ M)
  (hfactor : ∀ c : R.toStarSubalgebra, (∀ a, a * c = c * a) → ∃ z : ℂ, c = z • 1)
  (hdiff : ∀ p : R.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)
  (hirr : ∀ c : M.toStarSubalgebra,
    (∀ a : R.toStarSubalgebra, coordinateInclusion hRM a * c =
      c * coordinateInclusion hRM a) → ∃ z : ℂ, c = z • 1)

local instance quotientMomentAmbientClosed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance
local instance quotientMomentSourceClosed : IsClosed (R.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (R : Set (H →L[ℂ] H))
  infer_instance

include hfactor hdiff hirr in
theorem exists_centered_source_moment_sequence
    (A : ℕ → (ℕ →ᵇ M.toStarSubalgebra)) (hA : ∀ i n, ‖A i n‖ ≤ 1) :
    ∃ u : ℕ → unitary R.toStarSubalgebra, ∀ m K N : ℕ,
      ∀ a : BoundedWord (Fin m) K N, admissibleTail a.2.val →
      Tendsto (fun n => (vectorPositiveFunctional M υ.vector) (mixedEval
        (fun i : Fin m => (1 / 2 : ℂ) • (A i.val n - υ.trace (A i.val n) • 1))
        (asPartialUnitary (mapUnitary (coordinateInclusion hRM) (u n))) a.1 a.2.val))
        atTop (𝓝 0) := by
  let τ := vectorPositiveFunctional M υ.vector
  let F : ℕ → ℕ → M.toStarSubalgebra := fun n i => (1 / 2 : ℂ) • (A i n - τ (A i n) • 1)
  obtain ⟨u, hu⟩ := exists_source_small_moment_sequence υ hRM hfactor hdiff hirr F
    (fun n i => norm_centered_half τ υ.trace_one (A i n) (hA i n))
    (fun n i => trace_centered_half τ υ.trace_one (A i n))
  refine ⟨u, ?_⟩
  intro m K N a ha
  have h := hu m K N a ha
  simp only [source_map_asPartialUnitary] at h
  exact h

include hfactor hdiff hirr in
/-- A sequence from the source annihilates all fixed finite quotient words
in a countable family of centered ambient bounded sequences. -/
theorem exists_source_quotient_unitary_moments
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (A : ℕ → (ℕ →ᵇ M.toStarSubalgebra)) (hA : ∀ i n, ‖A i n‖ ≤ 1) :
    ∃ u : ℕ → unitary R.toStarSubalgebra,
      FiniteQuotientMoments (B := M.toStarSubalgebra) (vectorPositiveFunctional M υ.vector) υ.trace_one ω υ.trace_mul_comm
        A (fun n => mapUnitary (coordinateInclusion hRM) (u n)) := by
  obtain ⟨u, hu⟩ := exists_centered_source_moment_sequence υ hRM hfactor hdiff hirr A hA
  exact ⟨u, finiteQuotientMoments_of_limits (B := M.toStarSubalgebra) (vectorPositiveFunctional M υ.vector)
    υ.trace_one ω υ.trace_mul_comm hω A
    (fun n => mapUnitary (coordinateInclusion hRM) (u n)) hu⟩

end KadisonSimilarity

end

end OAI

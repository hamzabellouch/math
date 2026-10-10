import OAI.NumberTheory.DukePrimeDegree.Geometry.SmallCompactHeight
import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteLevelFutureLifts

namespace OAI

/-! # Geometric future observations with a small-entropy level label

The countable observation is finite on compact height ranges and its
whole-future fibers lie in triangular right orbits. Its height label can
have arbitrarily small entropy at every finite truncation. No finite
Shannon entropy of the complete countable observation is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_low_height_entropy_triangular_observation (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) {ε : ℝ} (hε : 0 < ε) :
    ∃ H Q : X (d+1) → ℕ, Measurable H ∧ Measurable Q ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N : ℕ, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      ∀ x y, (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
            Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G (d+1), rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0 := by
  have hT : MeasurePreserving
      (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨H,hH,hK,hent⟩ := exists_compact_height_small_entropy μ _ hT hε
  obtain ⟨Q,hQ,hfinite,htri⟩ := exists_finite_level_triangular_observation ell hell H hH hK
  exact ⟨H,Q,hH,hQ,hK,hfinite,hent,htri⟩

end DukePrimeDegree

end

end OAI

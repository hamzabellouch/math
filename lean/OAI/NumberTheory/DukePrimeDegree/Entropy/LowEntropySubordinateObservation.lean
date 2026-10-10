import OAI.NumberTheory.DukePrimeDegree.Entropy.ControlledSubordinateObservation
import OAI.NumberTheory.DukePrimeDegree.Entropy.LowEntropyRadialHeight

namespace OAI

/-! # Subordinate countable observations with small-entropy height labels -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_low_entropy_subordinate_observation (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H Q : X (d+1) → ℕ, Measurable H ∧ Measurable Q ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G (d+1), rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0) ∧
      ∀ᵐ x ∂μ, ∀ᶠ s in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word s))) =
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x) := by
  let a := diagonalOneParameter ell hell (-1)
  have hT : MeasurePreserving (fun x => rightAction x a) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [a]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨B,D,t,H,hB,hD,hH,ht,hlevel,hcompact,hstep,hnull,hbound,hent⟩ :=
    exists_low_entropy_controlled_radial_height μ a hT hε
  have hheight (x : X (d+1)) :
      quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B :=
    ((hlevel x (H x)).mp le_rfl).trans (ht (H x))
  obtain ⟨r₀,hr₀,hr₀1,htri⟩ := exists_radial_radius_triangular_lifts
    (Nat.succ_pos d) ell hell B hB H hheight
  obtain ⟨Q,hQ,hfinite,hsmall,hgood⟩ := exists_controlled_root_future_observation
    d ell hell hgap μ hA B hB H hH t ht hlevel (fun x => (hstep x).1)
    hnull hD hbound hr₀ hr₀1
  exact ⟨H,Q,hH,hQ,hcompact,hfinite,hent,
    htri Q (fun x y hxy => (hsmall x y hxy).2),hgood⟩

end DukePrimeDegree

end

end OAI

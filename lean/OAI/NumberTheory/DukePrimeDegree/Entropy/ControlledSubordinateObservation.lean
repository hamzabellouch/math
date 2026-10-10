import OAI.NumberTheory.DukePrimeDegree.Entropy.ControlledRootFuture
import OAI.NumberTheory.DukePrimeDegree.Geometry.ControlledRadialHeight
import OAI.NumberTheory.DukePrimeDegree.Entropy.RadialFutureLifts
import OAI.NumberTheory.DukePrimeDegree.Geometry.CountableRootPrefixAtoms

namespace OAI

/-! # One countable observation with both future-fiber properties

The same observation has triangular relative lifts and contains an open
upper-root neighborhood in almost every whole-future atom. Its auxiliary
proper height is sublinear on almost every invariant orbit.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_controlled_subordinate_observation (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    ∃ H Q : X (d+1) → ℕ, Measurable H ∧ Measurable Q ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ᵐ x ∂μ, Tendsto (fun k : ℕ =>
        (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x):ℝ) /
          (k:ℝ)) atTop (𝓝 0)) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g : G (d+1), rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0) ∧
      ∀ᵐ x ∂μ, ∀ᶠ s in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word s))) =
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x) := by
  let a := diagonalOneParameter ell hell (-1)
  obtain ⟨B,t,H,hB,_,hH,ht,hlevel,hcompact,hstep,hboundary⟩ :=
    exists_controlled_radial_height μ a
  have hlev (x : X (d+1)) (m : ℕ) : H x ≤ m ↔
      quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ t m := by
    change x ∈ {x | H x ≤ m} ↔
      x ∈ {x | quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ t m}
    rw [hlevel m]
  have hupper (m : ℕ) : t m ≤ 2*B*(m:ℝ)+B := by
    have hh := (ht m).2
    nlinarith
  have hheight (x : X (d+1)) :
      quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B :=
    ((hlev x (H x)).mp le_rfl).trans (hupper (H x))
  obtain ⟨r₀,hr₀,hr₀1,htri⟩ := exists_radial_radius_triangular_lifts
    (Nat.succ_pos d) ell hell B hB H hheight
  obtain ⟨Q,hQ,hfinite,hsmall,hgood⟩ := exists_controlled_root_future_observation
    d ell hell hgap μ hA B hB H hH t hupper hlev (fun x => (hstep x).1)
    (fun m => (hboundary m).1) (by positivity) (fun m k => (hboundary m).2 k) hr₀ hr₀1
  have hT : MeasurePreserving (fun x => rightAction x a) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [a]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  exact ⟨H,Q,hH,hQ,hcompact,hfinite,
    ae_height_div_tendsto_zero μ hT H hH (fun x => (hstep x).1),
    htri Q (fun x y hxy => (hsmall x y hxy).2),hgood⟩

end DukePrimeDegree

end

end OAI

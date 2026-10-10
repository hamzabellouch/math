import OAI.Combinatorics.ExpectationThreshold.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# Compactness of the fractional feasible densities

The cover coefficients and the density range over closed unit intervals.
The coverage inequalities and the polynomial cost bound cut out a closed
subset of their compact product. Its projection is exactly the set of
fractionally feasible densities, including when that set is empty.
-/

namespace TalagrandThreshold

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The fractional cost is jointly continuous in the density and coefficients. -/
theorem continuous_fracCost :
    Continuous (fun z : ℝ × (Finset α → ℝ) => fracCost z.1 z.2) := by
  unfold fracCost
  exact continuous_finsetSum Finset.univ fun S _ =>
    ((continuous_apply S).comp continuous_snd).mul (continuous_fst.pow S.card)

omit [DecidableEq α] in
/-- Fractional feasibility is the projection of the actual compact set of covers. -/
theorem isCompact_fractionalFeasible (F : Family α) :
    IsCompact (fractionalFeasible F) := by
  let B : Set (ℝ × (Finset α → ℝ)) :=
    Set.Icc (0 : ℝ) 1 ×ˢ {g | ∀ S, 0 ≤ g S ∧ g S ≤ 1}
  let C : Set (ℝ × (Finset α → ℝ)) :=
    {z | (∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, z.2 S) ∧ fracCost z.1 z.2 ≤ 1 / 2}
  have hbox : IsCompact B :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).prod
      (isCompact_pi_infinite fun _ : Finset α =>
        (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)))
  have hcoverage : IsClosed
      {z : ℝ × (Finset α → ℝ) | ∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, z.2 S} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun H => isClosed_iInter fun _ => ?_
    exact isClosed_le continuous_const
      (continuous_finsetSum H.powerset fun S _ =>
        (continuous_apply S).comp continuous_snd)
  have hcost : IsClosed
      {z : ℝ × (Finset α → ℝ) | fracCost z.1 z.2 ≤ 1 / 2} :=
    isClosed_le continuous_fracCost continuous_const
  have hclosed : IsClosed C := hcoverage.inter hcost
  have himage : Prod.fst '' (B ∩ C) = fractionalFeasible F := by
    ext p
    constructor
    · rintro ⟨⟨q, g⟩, ⟨hB, hC⟩, hp⟩
      change (0 ≤ q ∧ q ≤ 1) ∧ (∀ S, 0 ≤ g S ∧ g S ≤ 1) at hB
      change (∀ H ∈ F, 1 ≤ ∑ S ∈ H.powerset, g S) ∧ fracCost q g ≤ 1 / 2 at hC
      change q = p at hp
      subst p
      exact ⟨hB.1.1, hB.1.2, g, ⟨hB.2, hC.1⟩, hC.2⟩
    · rintro ⟨hp0, hp1, g, hcover, hcost⟩
      exact ⟨(p, g), ⟨⟨⟨hp0, hp1⟩, hcover.1⟩, ⟨hcover.2, hcost⟩⟩, rfl⟩
  rw [← himage]
  exact (hbox.inter_right hclosed).image continuous_fst

end
end TalagrandThreshold

end OAI

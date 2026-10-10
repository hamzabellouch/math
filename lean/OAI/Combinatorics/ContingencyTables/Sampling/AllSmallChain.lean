import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallFibres
import OAI.Combinatorics.ContingencyTables.Sampling.UnitGraphEnergy

namespace OAI

/-! # The small-state walk when no dense completion remains

Every retained completion then has weight one. The same local graph is
sampled by accepting every valid proposal; no reference row is chosen.
-/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts CommonBasesFPRAS FiniteExposureVariance

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
local notation "d" => dimensionAllowance (I := I) (J := J)
local instance : DecidableEq (PaperStates r c) := Classical.decEq _

local notation "Adj" => physicalAdjacent r c (d^20) (d^12) (stateCapacity r c) (stateCapacity_small r c)

def unitSmallChain : FiniteChain (PaperStates r c) :=
  MetropolisChain.chain (fun _ => 1) (fun _ => by norm_num) Adj
    (physicalAdjacent_symmetric r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal d) ((smallProposal_bounds d (by unfold dimensionAllowance; omega)).1.le)
    (5*d^2+1)
    (physicalAdjacent_degree_allowance r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal_degree d (by unfold dimensionAllowance; omega))

lemma unitSmallChain_pi (z : PaperStates r c) :
    (unitSmallChain r c).π z=1/(Fintype.card (PaperStates r c):ℝ) := by
  simp only [unitSmallChain,MetropolisChain.chain,FiniteChain.ofMoves,
    MetropolisChain.normalizer,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

lemma unitSmallChain_energy (H : PaperStates r c → ℝ) :
    (unitSmallChain r c).energy H=
      (smallProposal d/(Fintype.card (PaperStates r c):ℝ))*
        ((∑ x,∑ y,if Adj x y then (H x-H y)^2 else 0)/2) := by
  exact MetropolisChain.unit_chain_energy Adj
    (physicalAdjacent_symmetric r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal d) ((smallProposal_bounds d (by unfold dimensionAllowance; omega)).1.le)
    (5*d^2+1)
    (physicalAdjacent_degree_allowance r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal_degree d (by unfold dimensionAllowance; omega)) H

omit [Nonempty (PaperStates r c)] in
lemma stateGraphEnergy_allSmall (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (H : PaperStates r c → ℝ) :
    stateGraphEnergy r c H=(∑ x,∑ y,if Adj x y then (H x-H y)^2 else 0)/2 := by
  have he := fullEnergy_physical_eq r c (d^20) (d^12) (stateCapacity r c) (stateCapacity_small r c) H
  change stateGraphEnergy r c H=(∑ x,∑ y,if Adj x y then
    min (stateWeight r c x) (stateWeight r c y)*(H x-H y)^2 else 0)/2 at he
  simpa only [stateWeight_allSmall r c hsmall,min_self,one_mul] using he

omit [LinearOrder I] [LinearOrder J] [Nonempty (PaperStates r c)] in
lemma allowance_fourteen [Nonempty I] [Nonempty J] : 14 ≤ d := by
  have hi := Fintype.card_pos (α := I)
  have hj := Fintype.card_pos (α := J)
  unfold dimensionAllowance
  nlinarith

lemma unitSmallChain_pi_weight
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true) (z : PaperStates r c) :
    (unitSmallChain r c).π z=stateWeight r c z/(∑ y,stateWeight r c y) := by
  rw [unitSmallChain_pi]
  simp only [stateWeight_allSmall r c hsmall,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

lemma unitSmallChain_energy_lower
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (H : PaperStates r c → ℝ) :
    (smallProposal d)/(2*(∑ z,stateWeight r c z))*stateGraphEnergy r c H ≤
      (unitSmallChain r c).energy H := by
  have hsum : (∑ z,stateWeight r c z)=(Fintype.card (PaperStates r c):ℝ) := by
    simp only [stateWeight_allSmall r c hsmall,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have hi := unitSmallChain_energy r c H
  rw [←stateGraphEnergy_allSmall r c hsmall H] at hi
  rw [hsum]
  calc
    _ = ((smallProposal d/(Fintype.card (PaperStates r c):ℝ))*stateGraphEnergy r c H)/2 := by ring
    _ = (unitSmallChain r c).energy H/2 := by rw [hi]
    _ ≤ (unitSmallChain r c).energy H := by linarith [(unitSmallChain r c).energy_nonneg H]

/-- The full graph bound includes the empty large rectangle. -/
theorem unitSmallChain_poincare [Nonempty I] [Nonempty J]
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (H : PaperStates r c → ℝ) :
    (unitSmallChain r c).variance H ≤ (d:ℝ)^160*(unitSmallChain r c).energy H := by
  let K : ℝ := 770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6
  have hβ := (smallProposal_bounds d (by unfold dimensionAllowance; omega)).1
  have hv : variance (stateWeight r c) H ≤ K*stateGraphEnergy r c H :=
    firstPaper_physical_variance r c H
  have hp := chain_poincare_of_weighted_graph (unitSmallChain r c) (stateWeight r c) H
    (stateWeight_positive r c) (unitSmallChain_pi_weight r c hsmall)
    (stateGraphEnergy r c H) K (smallProposal d) (by dsimp [K]; positivity) hβ hv
    (unitSmallChain_energy_lower r c hsmall H)
  exact hp.trans (mul_le_mul_of_nonneg_right
    (smallProposal_poincare_budget d allowance_fourteen) ((unitSmallChain r c).energy_nonneg H))

end
end ContingencyTables.SmallGraphProfiles

end OAI

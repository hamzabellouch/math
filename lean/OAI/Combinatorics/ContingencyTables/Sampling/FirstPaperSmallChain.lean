import OAI.Combinatorics.ContingencyTables.Transport.ReferenceEdgeAcceptance
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalPaperCapacity
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalSmallEnergy
import OAI.Combinatorics.ContingencyTables.Transport.CompletionEnergyComparison
import OAI.Combinatorics.ContingencyTables.Transport.FiniteChainGraphComparison
import OAI.Combinatorics.ContingencyTables.Sampling.SmallProposal

namespace OAI

/-! # The literal first-paper completion chain has the stated Poincare bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CommonBasesFPRAS PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open CompletionTranslation FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable abbrev stateCapacity (r : I → ℕ) (c : J → ℕ) : I → J → ℕ :=
  paperCapacity (paperSmall r c) r (dimensionAllowance (I := I) (J := J))
    ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20)

abbrev PaperStates (r : I → ℕ) (c : J → ℕ) :=
  PhysicalStates (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)

/-- Keep one public enumeration instance for the paper's state type, so
rational laws and generic finite kernels share the same index. -/
noncomputable instance paperStatesFintype (r : I → ℕ) (c : J → ℕ) :
    Fintype (PaperStates r c) :=
  physicalStatesFintype (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)

omit [LinearOrder I] [LinearOrder J] in
lemma stateCapacity_small (r : I → ℕ) (c : J → ℕ) (i : I) (j : J)
    (h : paperSmall r c i j=true) :
    stateCapacity r c i j=(dimensionAllowance (I := I) (J := J))^20 := by
  simp only [stateCapacity,paperCapacity,h,ite_true]

noncomputable def paperSmallChain (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20)) :
    FiniteChain (PaperStates r c) :=
  completionChain
    (referenceRows r c _ _ (stateCapacity r c) i₀)
    (referenceColumns r c _ _ (stateCapacity r c) j₀)
    (fun z => reference_totals r c _ _ (stateCapacity r c) i₀ j₀ z
      (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z))
    (physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (physicalAdjacent_symmetric r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal (dimensionAllowance (I := I) (J := J)))
    ((smallProposal_bounds _ (by unfold dimensionAllowance; omega)).1.le)
    (5*(dimensionAllowance (I := I) (J := J))^2+1)
    (physicalAdjacent_degree_allowance r c _ _ (stateCapacity r c) (stateCapacity_small r c))
    (smallProposal_degree _ (by unfold dimensionAllowance; omega))

noncomputable def stateWeight (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) : ℝ :=
  hardMarginal (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z)

noncomputable def stateGraphEnergy (r : I → ℕ) (c : J → ℕ) (H : PaperStates r c → ℝ) : ℝ :=
  fullEnergy r c ((dimensionAllowance (I := I) (J := J))^20)
    ((dimensionAllowance (I := I) (J := J))^12) (stateCapacity r c)
    (stateCapacity_small r c) (physicalExtension _ (stateCapacity r c) r c _ H)

lemma stateWeight_positive (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) :
    0 < stateWeight r c z := z.property

lemma paperSmallChain_pi (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (z : PaperStates r c) :
    (paperSmallChain r c i₀ j₀).π z=stateWeight r c z/(∑ y,stateWeight r c y) := by
  have hw (y : PaperStates r c) := physical_weight_reference_block r c _ _ (stateCapacity r c)
    i₀ j₀ y (physical_paper_capacity _ r c _ _ _ dimension_le_allowance y)
  change _=hardMarginal _ _ _ _ _ _/(∑ y,hardMarginal _ _ _ _ _ _)
  simp_rw [hw]
  rfl

lemma paperSmallChain_energy_lower (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (H : PaperStates r c → ℝ) :
    smallProposal (dimensionAllowance (I := I) (J := J))/(2*(∑ z,stateWeight r c z))*
      stateGraphEnergy r c H ≤ (paperSmallChain r c i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let L := d^12
  let B := stateCapacity r c
  let R := referenceRows r c U L B i₀
  let P := referenceColumns r c U L B j₀
  have hcap := physical_paper_capacity (paperSmall r c) r c d L U dimension_le_allowance
  have hw (z : PaperStates r c) : stateWeight r c z=(blockCount R P z:ℝ) :=
    physical_weight_reference_block r c U L B i₀ j₀ z (hcap z)
  have hh := completionChain_energy_lower R P
    (fun z => reference_totals r c U L B i₀ j₀ z (hcap z))
    (physicalAdjacent r c U L B (stateCapacity_small r c))
    (physicalAdjacent_symmetric r c U L B (stateCapacity_small r c))
    (smallProposal d) ((smallProposal_bounds d (by dsimp [d,dimensionAllowance]; omega)).1.le)
    (5*d^2+1)
    (physicalAdjacent_degree_allowance r c U L B (stateCapacity_small r c))
    (smallProposal_degree d (by dsimp [d,dimensionAllowance]; omega))
    (reference_edge_acceptance r c U B (stateCapacity_small r c) i₀ j₀ hcap) H
  have hE := fullEnergy_physical_eq r c U L B (stateCapacity_small r c) H
  change stateGraphEnergy r c H=(∑ x,∑ y,
    if physicalAdjacent r c U L B (stateCapacity_small r c) x y then
      min (stateWeight r c x) (stateWeight r c y)*(H x-H y)^2 else 0)/2 at hE
  rw [hE]
  simp_rw [hw]
  exact hh

/-- Every observable on the actual positive completion states satisfies
 the source's `d^160` bound, with the actual dyadic proposal probability. -/
theorem paperSmallChain_poincare (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (H : PaperStates r c → ℝ) :
    (paperSmallChain r c i₀ j₀).variance H ≤
      (dimensionAllowance (I := I) (J := J):ℝ)^160*(paperSmallChain r c i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let K := 770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6
  have hv : variance (stateWeight r c) H ≤ K*stateGraphEnergy r c H :=
    firstPaper_physical_variance r c H
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hb := smallProposal_bounds d (by dsimp [d,dimensionAllowance]; omega)
  have hp := chain_poincare_of_weighted_graph (paperSmallChain r c i₀ j₀)
    (stateWeight r c) H (stateWeight_positive r c) (paperSmallChain_pi r c i₀ j₀)
    (stateGraphEnergy r c H) K (smallProposal d) hK hb.1 hv
    (paperSmallChain_energy_lower r c i₀ j₀ H)
  exact hp.trans (mul_le_mul_of_nonneg_right
    (smallProposal_poincare_budget d (reference_dimension_ge_fourteen r c _ i₀ j₀))
    ((paperSmallChain r c i₀ j₀).energy_nonneg H))

end ContingencyTables.SmallGraphProfiles

end OAI

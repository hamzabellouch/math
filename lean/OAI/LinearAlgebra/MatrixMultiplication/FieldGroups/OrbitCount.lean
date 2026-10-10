import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.OrbitCount
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Priority

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev GroupClasses (K tick : ℕ) (sigma : Placement) :=
  ActiveOrder K tick sigma × JointPopulation.Shape

abbrev GroupPositions {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    {sigma : Placement} (c : GroupClasses K tick sigma) :=
  Fin (activeCounts allocation m c.1.val c.2)

abbrev GroupLetters {K tick : ℕ} {sigma : Placement} (c : GroupClasses K tick sigma) :=
  Fin (activeHalfLength c.1.val) → Fin 7

abbrev GroupOrbit {K tick : ℕ} (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  PairOrbit (GroupPositions (K := K) (tick := tick) (sigma := sigma) allocation m)
    (GroupLetters (K := K) (tick := tick) (sigma := sigma))
    (GroupLetters (K := K) (tick := tick) (sigma := sigma))

noncomputable instance groupOrbitFintype {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Fintype (GroupOrbit (K := K) (tick := tick) allocation m sigma) := by
  haveI : Finite (GroupOrbit (K := K) (tick := tick) allocation m sigma) :=
    Finite.of_injective pairOrbitProfile pairOrbitProfile_injective
  exact Fintype.ofFinite _

def groupDegree (K tick : ℕ) (sigma : Placement) : ℕ :=
  2 * ∑ c : GroupClasses K tick sigma, 7 ^ activeHalfLength c.1.val

theorem card_groupLetters {K tick : ℕ} {sigma : Placement}
    (c : GroupClasses K tick sigma) :
    Fintype.card (GroupLetters c) = 7 ^ activeHalfLength c.1.val := by
  simp only [GroupLetters, Fintype.card_fun, Fintype.card_fin]

theorem groupClass_card_le {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    {sigma : Placement} (c : GroupClasses K tick sigma) :
    Fintype.card (GroupPositions allocation m c) ≤
      AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation * m :=
  AllFieldHistoryOrbitCount.class_card_le allocation m (c.1.val, c.2)

theorem card_groupOrbit_le {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) ≤
      (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation * m + 1) ^
        groupDegree K tick sigma := by
  simpa only [GroupOrbit, groupDegree, card_groupLetters, two_mul] using
    (card_pairOrbits_le_common_bound
      (P := GroupPositions (K := K) (tick := tick) (sigma := sigma) allocation m)
      (X := GroupLetters (K := K) (tick := tick) (sigma := sigma))
      (Y := GroupLetters (K := K) (tick := tick) (sigma := sigma))
      (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation * m)
      (groupClass_card_le allocation m))

theorem card_groupOrbit_le_polynomial {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) ≤
      (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation + 1) ^
        groupDegree K tick sigma * (m + 1) ^ groupDegree K tick sigma := by
  refine (card_groupOrbit_le allocation m sigma).trans ?_
  rw [← mul_pow]
  apply Nat.pow_le_pow_left
  nlinarith [Nat.zero_le
    (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation)]

def groupOrbitPrefactor {K tick : ℕ} (allocation : Allocation) (sigma : Placement) : ℝ :=
  ((AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation + 1 : ℕ) : ℝ) ^
    groupDegree K tick sigma

theorem groupOrbitPrefactor_pos {K tick : ℕ} (allocation : Allocation) (sigma : Placement) :
    0 < groupOrbitPrefactor (K := K) (tick := tick) allocation sigma := by
  unfold groupOrbitPrefactor
  positivity

theorem card_groupOrbit_le_polynomial_real {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    (Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) ≤
      groupOrbitPrefactor (K := K) (tick := tick) allocation sigma *
        ((m : ℝ) + 1) ^ groupDegree K tick sigma := by
  unfold groupOrbitPrefactor
  exact_mod_cast card_groupOrbit_le_polynomial (K := K) (tick := tick) allocation m sigma

theorem usedGroupOrbits_card_le_real {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (sigma : Placement)
    (s : Finset (GroupOrbit (K := K) (tick := tick) allocation m sigma)) :
    (s.card : ℝ) ≤ groupOrbitPrefactor (K := K) (tick := tick) allocation sigma *
      ((m : ℝ) + 1) ^ groupDegree K tick sigma := by
  have hs : s.card ≤ Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) := by
    rw [Nat.card_eq_fintype_card]
    exact s.card_le_univ
  have hsreal : (s.card : ℝ) ≤
      (Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) := by
    exact_mod_cast hs
  exact hsreal.trans (card_groupOrbit_le_polynomial_real allocation m sigma)

theorem taggedUsedGroupOrbits_card_le_real {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (s : Finset (Fin 3 × GroupOrbit (K := K) (tick := tick) allocation m sigma)) :
    (s.card : ℝ) ≤ (3 * groupOrbitPrefactor (K := K) (tick := tick) allocation sigma) *
      ((m : ℝ) + 1) ^ groupDegree K tick sigma := by
  have hs : s.card ≤ 3 * Nat.card
      (GroupOrbit (K := K) (tick := tick) allocation m sigma) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.card_eq_fintype_card] using
      s.card_le_univ
  have hsreal : (s.card : ℝ) ≤ 3 * (Nat.card
      (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) := by
    exact_mod_cast hs
  calc
    _ ≤ 3 * (Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) := hsreal
    _ ≤ 3 * (groupOrbitPrefactor (K := K) (tick := tick) allocation sigma *
        ((m : ℝ) + 1) ^ groupDegree K tick sigma) :=
      mul_le_mul_of_nonneg_left (card_groupOrbit_le_polynomial_real allocation m sigma)
        (by norm_num)
    _ = _ := (mul_assoc _ _ _).symm

end MatrixMultiplication.AllFieldGroupOrbitCount

end

end OAI

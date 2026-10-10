import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Support
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedOrbitProfiles

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Classes (K tick : ℕ) := ActiveClass K tick

abbrev Positions {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (c : Classes K tick) :=
  JointCanonicalization.ClassPositions (activeCounts allocation m) c

abbrev Letters {K tick : ℕ} (c : Classes K tick) :=
  Fin (activeHalfLength c.1) → Fin 7

abbrev ActualOrbit {K tick : ℕ} (allocation : Allocation) (m : ℕ) :=
  PairOrbit (Positions (K := K) (tick := tick) allocation m)
    (Letters (K := K) (tick := tick)) (Letters (K := K) (tick := tick))

noncomputable instance actualOrbitFintype {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) :
    Fintype (ActualOrbit (K := K) (tick := tick) allocation m) := by
  haveI : Finite (ActualOrbit (K := K) (tick := tick) allocation m) :=
    Finite.of_injective pairOrbitProfile pairOrbitProfile_injective
  exact Fintype.ofFinite _

def basePopulationBound {K tick : ℕ} (allocation : Allocation) : ℕ :=
  ∑ c : Classes K tick, activeCounts allocation 1 c.1 c.2

def orbitDegree (K tick : ℕ) : ℕ :=
  2 * ∑ c : Classes K tick, 7 ^ activeHalfLength c.1

theorem card_letters {K tick : ℕ} (c : Classes K tick) :
    Fintype.card (Letters c) = 7 ^ activeHalfLength c.1 := by
  simp only [Letters, Fintype.card_fun, Fintype.card_fin]

theorem class_card_le {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (c : Classes K tick) :
    Fintype.card (Positions allocation m c) ≤
      basePopulationBound (K := K) (tick := tick) allocation * m := by
  have hc : activeCounts allocation 1 c.1 c.2 ≤
      basePopulationBound (K := K) (tick := tick) allocation := by
    unfold basePopulationBound
    exact Finset.single_le_sum
      (fun (d : Classes K tick) _ => Nat.zero_le (activeCounts allocation 1 d.1 d.2))
      (Finset.mem_univ c)
  simp only [Positions, JointCanonicalization.ClassPositions, Fintype.card_fin,
    activeCounts_dilation allocation m]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left m hc

theorem card_actualOrbit_le {K tick : ℕ} (allocation : Allocation) (m : ℕ) :
    Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) ≤
      (basePopulationBound (K := K) (tick := tick) allocation * m + 1) ^
        orbitDegree K tick := by
  simpa only [ActualOrbit, orbitDegree, card_letters, two_mul] using
    (card_pairOrbits_le_common_bound
      (P := Positions (K := K) (tick := tick) allocation m)
      (X := Letters (K := K) (tick := tick))
      (Y := Letters (K := K) (tick := tick))
      (basePopulationBound (K := K) (tick := tick) allocation * m)
      (class_card_le allocation m))

theorem card_actualOrbit_le_polynomial {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) :
    Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) ≤
      (basePopulationBound (K := K) (tick := tick) allocation + 1) ^ orbitDegree K tick *
        (m + 1) ^ orbitDegree K tick := by
  refine (card_actualOrbit_le allocation m).trans ?_
  rw [← mul_pow]
  apply Nat.pow_le_pow_left
  nlinarith [Nat.zero_le (basePopulationBound (K := K) (tick := tick) allocation)]

def orbitPrefactor {K tick : ℕ} (allocation : Allocation) : ℝ :=
  ((basePopulationBound (K := K) (tick := tick) allocation + 1 : ℕ) : ℝ) ^
    orbitDegree K tick

theorem orbitPrefactor_pos {K tick : ℕ} (allocation : Allocation) :
    0 < orbitPrefactor (K := K) (tick := tick) allocation := by
  unfold orbitPrefactor
  positivity

theorem card_actualOrbit_le_polynomial_real {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) :
    (Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) : ℝ) ≤
      orbitPrefactor (K := K) (tick := tick) allocation *
        ((m : ℝ) + 1) ^ orbitDegree K tick := by
  unfold orbitPrefactor
  exact_mod_cast card_actualOrbit_le_polynomial (K := K) (tick := tick) allocation m

theorem usedOrbits_card_le {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (s : Finset (ActualOrbit (K := K) (tick := tick) allocation m)) :
    s.card ≤ (basePopulationBound (K := K) (tick := tick) allocation + 1) ^
      orbitDegree K tick * (m + 1) ^ orbitDegree K tick := by
  have hs : s.card ≤ Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) := by
    rw [Nat.card_eq_fintype_card]
    exact s.card_le_univ
  exact hs.trans (card_actualOrbit_le_polynomial allocation m)

theorem usedOrbits_card_le_real {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (s : Finset (ActualOrbit (K := K) (tick := tick) allocation m)) :
    (s.card : ℝ) ≤ orbitPrefactor (K := K) (tick := tick) allocation *
      ((m : ℝ) + 1) ^ orbitDegree K tick := by
  unfold orbitPrefactor
  exact_mod_cast usedOrbits_card_le allocation m s

theorem taggedUsedOrbits_card_le_real {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (s : Finset (Fin 3 × ActualOrbit (K := K) (tick := tick) allocation m)) :
    (s.card : ℝ) ≤ (3 * orbitPrefactor (K := K) (tick := tick) allocation) *
      ((m : ℝ) + 1) ^ orbitDegree K tick := by
  have hs : s.card ≤ 3 * Nat.card
      (ActualOrbit (K := K) (tick := tick) allocation m) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.card_eq_fintype_card] using
      s.card_le_univ
  have hsreal : (s.card : ℝ) ≤ 3 * (Nat.card
      (ActualOrbit (K := K) (tick := tick) allocation m) : ℝ) := by
    exact_mod_cast hs
  calc
    _ ≤ 3 * (Nat.card (ActualOrbit (K := K) (tick := tick) allocation m) : ℝ) := hsreal
    _ ≤ 3 * (orbitPrefactor (K := K) (tick := tick) allocation *
        ((m : ℝ) + 1) ^ orbitDegree K tick) :=
      mul_le_mul_of_nonneg_left (card_actualOrbit_le_polynomial_real allocation m)
        (by norm_num)
    _ = _ := (mul_assoc _ _ _).symm

end MatrixMultiplication.AllFieldHistoryOrbitCount

end

end OAI

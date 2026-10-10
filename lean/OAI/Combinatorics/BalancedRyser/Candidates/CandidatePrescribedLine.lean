import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Local.GlobalPartialAlignment
import OAI.Combinatorics.BalancedRyser.Probability.GeneratorEnumeration

namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section
open scoped Classical
open Finset PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Code (F : Type*) := (Fin 4 → Direction F) × (Fin 4 → Bool)

def exposedLaw (old : Finset (Direction F)) (a : MergedPairs F) :
    PMF (MergedPairs F) :=
  (offsetLaw F).filter {M | ∀ d, d ∈ old → M d = a d}
    (canonical_exposure_supported old a)

def Eligible (l : Line F) (c : Code F) : Prop :=
  Function.Injective c.1 ∧ ∀ i, c.1 i ≠ l.1

def alignmentMass (old : Finset (Direction F)) (a : MergedPairs F)
    (l : Line F) (c : Code F) : ℝ :=
  if Eligible l c then
    ((exposedLaw old a).toOuterMeasure
      {M | ∀ i, OnLine (tuplePoint M ⟨c.1, c.2⟩ i) l}).toReal
  else 0

theorem alignmentMass_nonneg (old : Finset (Direction F)) (a : MergedPairs F)
    (l : Line F) (c : Code F) : 0 ≤ alignmentMass old a l c := by
  unfold alignmentMass
  split_ifs <;> positivity

theorem fixedPositions_card_le (J : Finset (Fin 4)) :
    (fixedPositions J).card ≤ J.card := by
  apply Finset.card_le_card
  intro i hi
  exact (Finset.mem_filter.mp hi).2.1

theorem alignmentMass_le (old : Finset (Direction F)) (a : MergedPairs F)
    (l : Line F) (c : Code F) (j : ℕ)
    (hc : c ∈ tupleCodesWithOldCount old j) :
    alignmentMass old a l c ≤ (Fintype.card F : ℝ)⁻¹ ^ (4 - j) := by
  have hJ : (exposedTupleIndices (⟨c.1, c.2⟩ : FourTuple F) old).card = j :=
    (Finset.mem_filter.mp (Finset.mem_product.mp hc).1).2
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  unfold alignmentMass
  split_ifs with he
  · have h := canonical_conditional_alignment_probability_le
      (⟨c.1, c.2⟩ : FourTuple F) he.1 l.1 he.2 l.2 old a
    change _ ≤ _ at h
    apply h.trans
    apply pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hq)
    have hf := fixedPositions_card_le
      (exposedTupleIndices (⟨c.1, c.2⟩ : FourTuple F) old)
    rw [hJ] at hf
    omega
  · positivity

theorem card_codes_le (old : Finset (Direction F)) (j : ℕ) (hj : j ≤ 4) :
    (tupleCodesWithOldCount old j).card ≤
      (4096 * (old.card + 1) ^ 4) * Fintype.card F ^ (4 - j) := by
  have hchoose : Nat.choose 4 j ≤ 16 := by
    interval_cases j <;> decide
  have hpow : old.card ^ j ≤ (old.card + 1) ^ 4 := by
    calc
      old.card ^ j ≤ (old.card + 1) ^ j := Nat.pow_le_pow_left (by omega) j
      _ ≤ (old.card + 1) ^ 4 := Nat.pow_le_pow_right (by omega) hj
  have hdir : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
    have hq : 0 < Fintype.card F := Fintype.card_pos
    simp only [Direction, Fintype.card_option]
    omega
  have htwo : 2 ^ (4 - j) ≤ 16 := by
    calc
      2 ^ (4 - j) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 16 := rfl
  calc
    (tupleCodesWithOldCount old j).card ≤
        16 * (Nat.choose 4 j * old.card ^ j * Fintype.card (Direction F) ^ (4-j)) :=
      card_tupleCodesWithOldCount_le old j
    _ ≤ 16 * (16 * (old.card + 1) ^ 4 * (2 * Fintype.card F) ^ (4-j)) := by
      gcongr
    _ = 256 * (old.card + 1) ^ 4 * (2 ^ (4-j) * Fintype.card F ^ (4-j)) := by
      rw [Nat.mul_pow]
      ring
    _ ≤ 256 * (old.card + 1) ^ 4 * (16 * Fintype.card F ^ (4-j)) := by
      gcongr
    _ = _ := by ring

theorem sum_alignmentMass_stratum_le (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) (j : ℕ) (hj : j ≤ 4) :
    (∑ c ∈ tupleCodesWithOldCount old j, alignmentMass old a l c) ≤
      4096 * ((old.card : ℝ) + 1) ^ 4 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hcount : ((tupleCodesWithOldCount old j).card : ℝ) ≤
      (4096 * ((old.card : ℝ) + 1) ^ 4) * (Fintype.card F : ℝ) ^ (4-j) := by
    exact_mod_cast card_codes_le old j hj
  calc
    (∑ c ∈ tupleCodesWithOldCount old j, alignmentMass old a l c) ≤
        ∑ _c ∈ tupleCodesWithOldCount old j, (Fintype.card F : ℝ)⁻¹ ^ (4-j) := by
      exact Finset.sum_le_sum (fun c hc => alignmentMass_le old a l c j hc)
    _ = ((tupleCodesWithOldCount old j).card : ℝ) *
        (Fintype.card F : ℝ)⁻¹ ^ (4-j) := by simp
    _ ≤ ((4096 * ((old.card : ℝ) + 1) ^ 4) * (Fintype.card F : ℝ) ^ (4-j)) *
        (Fintype.card F : ℝ)⁻¹ ^ (4-j) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hq), one_pow, mul_one]

omit [Field F] in
theorem codes_stratum_eq_filter (old : Finset (Direction F)) (j : ℕ) :
    tupleCodesWithOldCount old j =
      (Finset.univ : Finset (Code F)).filter
        (fun c => (Finset.univ.filter (fun i => c.1 i ∈ old)).card = j) := by
  ext c
  simp [tupleCodesWithOldCount, generatorLabelsWithOldCount]

theorem sum_alignmentMass_le (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) :
    (∑ c : Code F, alignmentMass old a l c) ≤
      20480 * ((old.card : ℝ) + 1) ^ 4 := by
  have hpartition :
      (∑ j ∈ Finset.range 5, ∑ c ∈ tupleCodesWithOldCount old j,
        alignmentMass old a l c) = ∑ c : Code F, alignmentMass old a l c := by
    simp_rw [codes_stratum_eq_filter]
    apply Finset.sum_fiberwise_of_maps_to
    intro c _
    apply Finset.mem_range.mpr
    have h := Finset.card_le_univ (Finset.univ.filter (fun i : Fin 4 => c.1 i ∈ old))
    simp only [Fintype.card_fin] at h
    omega
  rw [← hpartition]
  calc
    _ ≤ ∑ _j ∈ Finset.range 5, 4096 * ((old.card : ℝ) + 1) ^ 4 := by
      apply Finset.sum_le_sum
      intro j hj
      exact sum_alignmentMass_stratum_le old a l j (by have h := Finset.mem_range.mp hj; omega)
    _ = _ := by simp; ring

def alignedCodes (M : MergedPairs F) (l : Line F) : Finset (Code F) :=
  Finset.univ.filter (fun c => Eligible l c ∧
    ∀ i, OnLine (tuplePoint M ⟨c.1, c.2⟩ i) l)

def successfulCodes (M : MergedPairs F) (l : Line F) : Finset (Code F) :=
  (alignedCodes M l).filter
    (fun c => Function.Injective (tuplePoint M ⟨c.1, c.2⟩))

theorem alignmentMass_eq_sum (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) (c : Code F) :
    alignmentMass old a l c =
      ∑ M : MergedPairs F, if c ∈ alignedCodes M l then (exposedLaw old a M).toReal else 0 := by
  by_cases he : Eligible l c
  · simp only [alignmentMass, ite_eq_left he, PMF.toOuterMeasure_apply_fintype]
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro M _
      simp only [alignedCodes, Finset.mem_filter, Finset.mem_univ, true_and, he,
        Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs <;> simp
    · intro M _
      simp only [Set.indicator_apply]
      split_ifs
      · exact PMF.apply_ne_top _ _
      · simp
  · simp [alignmentMass, he, alignedCodes]

theorem expected_alignedCodes_eq (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) :
    (∑ M : MergedPairs F,
      (exposedLaw old a M).toReal * ((alignedCodes M l).card : ℝ)) =
      ∑ c : Code F, alignmentMass old a l c := by
  simp_rw [alignmentMass_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem expected_successfulCodes_le (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) :
    (∑ M : MergedPairs F,
      (exposedLaw old a M).toReal * ((successfulCodes M l).card : ℝ)) ≤
      20480 * ((old.card : ℝ) + 1) ^ 4 := by
  calc
    _ ≤ ∑ M : MergedPairs F,
        (exposedLaw old a M).toReal * ((alignedCodes M l).card : ℝ) := by
      apply Finset.sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast Finset.card_filter_le (alignedCodes M l)
        (fun c => Function.Injective (tuplePoint M ⟨c.1, c.2⟩))
    _ = _ := expected_alignedCodes_eq old a l
    _ ≤ _ := sum_alignmentMass_le old a l

theorem expected_successfulCodes_le_of_card_le (old : Finset (Direction F))
    (a : MergedPairs F) (l : Line F) (m : ℕ) (hm : old.card ≤ m) :
    (∑ M : MergedPairs F,
      (exposedLaw old a M).toReal * ((successfulCodes M l).card : ℝ)) ≤
      20480 * ((m : ℝ) + 1) ^ 4 := by
  apply (expected_successfulCodes_le old a l).trans
  gcongr

end
end Balanced.CandidatePrescribed

end OAI

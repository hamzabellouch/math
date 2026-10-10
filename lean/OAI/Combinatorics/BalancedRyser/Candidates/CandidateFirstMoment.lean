import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExposure

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def eligibleTuples (g : Direction F) : Finset (FourTuple F) :=
  Finset.univ.filter (fun T => Function.Injective T.generator ∧ ∀ i, T.generator i ≠ g)

def tuplesWithExposure (g : Direction F) (D : Finset (Direction F)) (j : ℕ) :
    Finset (FourTuple F) :=
  (eligibleTuples g).filter (fun T => (exposedTupleIndices T D).card = j)

theorem card_tupleCodesWithOldCount_le_bounded (D : Finset (Direction F))
    (m j : ℕ) (hD : D.card ≤ m) (hj : j ≤ 4) :
    (tupleCodesWithOldCount D j).card ≤
      (4096 * (m + 1) ^ 4) * Fintype.card F ^ (4 - j) := by
  have hchoose : Nat.choose 4 j ≤ 16 := by interval_cases j <;> decide
  have hpow : D.card ^ j ≤ (m + 1) ^ 4 := by
    exact (Nat.pow_le_pow_left (by omega : D.card ≤ m + 1) j).trans
      (Nat.pow_le_pow_right (by omega) hj)
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hdir : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
    simp only [Direction, Fintype.card_option]
    omega
  have htwo : 2 ^ (4 - j) ≤ 16 := by
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 - j ≤ 4))
  calc
    (tupleCodesWithOldCount D j).card ≤
        16 * (Nat.choose 4 j * D.card ^ j * Fintype.card (Direction F) ^ (4 - j)) :=
      card_tupleCodesWithOldCount_le D j
    _ ≤ 16 * (16 * (m + 1) ^ 4 * (2 * Fintype.card F) ^ (4 - j)) := by gcongr
    _ = 16 * (16 * (m + 1) ^ 4 * (2 ^ (4 - j) * Fintype.card F ^ (4 - j))) := by rw [Nat.mul_pow]
    _ ≤ 16 * (16 * (m + 1) ^ 4 * (16 * Fintype.card F ^ (4 - j))) := by gcongr
    _ = _ := by ring

theorem card_tuplesWithExposure_le (g : Direction F) (D : Finset (Direction F))
    (m j : ℕ) (hD : D.card ≤ m) (hj : j ≤ 4) :
    (tuplesWithExposure g D j).card ≤
      (4096 * (m + 1) ^ 4) * Fintype.card F ^ (4 - j) := by
  apply le_trans (Finset.card_le_card_of_injOn
    (fun T : FourTuple F => (T.generator, T.side)) ?_ ?_)
    (card_tupleCodesWithOldCount_le_bounded D m j hD hj)
  · intro T hT
    have hjT := (Finset.mem_filter.mp hT).2
    change (T.generator, T.side) ∈ tupleCodesWithOldCount D j
    simpa [tupleCodesWithOldCount, generatorLabelsWithOldCount, exposedTupleIndices] using hjT
  · intro T _ U _ h
    cases T
    cases U
    cases h
    rfl

private theorem counting_alignment_scale (q : ℝ) (hq : 1 ≤ q) (j : ℕ) (hj : j ≤ 4) :
    q ^ (4 - j) * q⁻¹ ^ alignmentExponent j ≤ if j = 0 then q else 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  interval_cases j <;> norm_num [alignmentExponent] <;> field_simp <;> nlinarith

theorem success_sum_withExposure_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m j : ℕ) (hD : D.card ≤ m) (hj : j ≤ 4) :
    (∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (successfulInDirection T g)) ≤
      (4096 * (m + 1) ^ 4 : ℝ) * (if j = 0 then (Fintype.card F : ℝ) else 1) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  calc
    _ ≤ ∑ _T ∈ tuplesWithExposure g D j,
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hgood, hjT⟩ := Finset.mem_filter.mp hT
      obtain ⟨hinj, htarget⟩ := (Finset.mem_filter.mp hgood).2
      simpa only [hjT] using successful_probability_le T hinj g htarget D a
    _ = ((tuplesWithExposure g D j).card : ℝ) *
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by simp
    _ ≤ ((4096 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ) ^ (4 - j)) *
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m j hD hj
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (counting_alignment_scale _ hq j hj) (by positivity)

def successProbabilitySum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : ℝ :=
  ∑ T ∈ eligibleTuples g, conditionalProbability D a (successfulInDirection T g)

def overlapProbabilitySum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) : ℝ :=
  ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card),
    conditionalProbability D a (successfulInDirection T g)

theorem successProbabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    successProbabilitySum g D a ≤ (20480 * (m + 1) ^ 4 : ℝ) * Fintype.card F := by
  have hpartition := Finset.sum_fiberwise_of_maps_to
    (s := eligibleTuples g) (t := Finset.range 5)
    (g := fun T => (exposedTupleIndices T D).card)
    (fun T _ => Finset.mem_range.mpr (by
      have h := Finset.card_le_univ (exposedTupleIndices T D)
      simp only [Fintype.card_fin] at h
      omega))
    (fun T => conditionalProbability D a (successfulInDirection T g))
  unfold successProbabilitySum
  rw [← hpartition]
  change (∑ j ∈ Finset.range 5, ∑ T ∈ tuplesWithExposure g D j,
    conditionalProbability D a (successfulInDirection T g)) ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range 5,
        (4096 * (m + 1) ^ 4 : ℝ) * (if j = 0 then (Fintype.card F : ℝ) else 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact success_sum_withExposure_le g D a m j hD (by
        have := Finset.mem_range.mp hj
        omega)
    _ ≤ _ := by
      norm_num [Finset.sum_range_succ]
      have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
      have h := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ (m + 1) ^ 4)
      nlinarith

theorem overlapProbabilitySum_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    overlapProbabilitySum g D a ≤ (16384 * (m + 1) ^ 4 : ℝ) := by
  have hpartition := Finset.sum_fiberwise_eq_sum_filter (eligibleTuples g)
    (Finset.Icc 1 4) (fun T => (exposedTupleIndices T D).card)
    (fun T => conditionalProbability D a (successfulInDirection T g))
  have hfilter : (eligibleTuples g).filter
      (fun T => (exposedTupleIndices T D).card ∈ Finset.Icc 1 4) =
      (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card) := by
    apply Finset.filter_congr
    intro T _
    have h := Finset.card_le_univ (exposedTupleIndices T D)
    simp only [Fintype.card_fin] at h
    simp only [Finset.mem_Icc]
    omega
  rw [hfilter] at hpartition
  unfold overlapProbabilitySum
  rw [← hpartition]
  change (∑ j ∈ Finset.Icc 1 4, ∑ T ∈ tuplesWithExposure g D j,
    conditionalProbability D a (successfulInDirection T g)) ≤ _
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 4, (4096 * (m + 1) ^ 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj0, hj4⟩ := Finset.mem_Icc.mp hj
      have h := success_sum_withExposure_le g D a m j hD hj4
      simpa only [ite_eq_right (by omega : j ≠ 0), mul_one] using h
    _ = _ := by norm_num; ring

end
end Balanced.CandidateExposure

end OAI

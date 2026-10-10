import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConditionalMean
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateConditionalFreshIncidence
import OAI.Combinatorics.BalancedRyser.Probability.FullyExposedTargets

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open PartialAlignment TupleAlignment MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem conditionalProbability_mono (D : Finset (Direction F)) (a : MergedPairs F)
    {E H : Set (MergedPairs F)} (h : E ⊆ H) :
    conditionalProbability D a E ≤ conditionalProbability D a H := by
  apply ENNReal.toReal_mono _ ((exposedLaw D a).toOuterMeasure.mono h)
  change (exposedLaw D a).toOuterMeasure H ≠ ⊤
  rw [PMF.toOuterMeasure_apply]
  exact (exposedLaw D a).tsum_coe_indicator_ne_top H

def successfulLineHit (T : FourTuple F) (g : Direction F) (L : Line F) :
    Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection T g ∧ ∃ i, OnLine (tuplePoint M T i) L}

theorem lineHit_probability_le_success (T : FourTuple F) (g : Direction F)
    (L : Line F) (D : Finset (Direction F)) (a : MergedPairs F) :
    conditionalProbability D a (successfulLineHit T g L) ≤
      conditionalProbability D a (successfulInDirection T g) :=
  conditionalProbability_mono D a (fun _ h => h.1)

theorem lineHit_probability_fresh_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : (exposedTupleIndices T D).card = 0) :
    conditionalProbability D a (successfulLineHit T g L) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have hnone : ∀ i, T.generator i ∉ D := by
    intro i hi
    have hempty := Finset.card_eq_zero.mp hfresh
    have hm : i ∈ exposedTupleIndices T D := by simp [exposedTupleIndices, hi]
    simp only [hempty, Finset.notMem_empty] at hm
  apply (conditionalProbability_mono D a (H :=
    {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, OnLine (tuplePoint M T i) L}) (fun _ h => ⟨h.1.1,h.2⟩)).trans
  exact CandidateFreshIncidence.conditional_tuple_hits_line_probability_le
    T hT D a hnone g L

theorem lineHit_sum_fresh_le (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ T ∈ tuplesWithExposure g D 0,
      conditionalProbability D a (successfulLineHit T g L)) ≤
        (16384 * (m + 1) ^ 4 : ℝ) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _T ∈ tuplesWithExposure g D 0, 4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hgood, hfresh⟩ := Finset.mem_filter.mp hT
      exact lineHit_probability_fresh_le T (Finset.mem_filter.mp hgood).2.1 g L D a hfresh
    _ = ((tuplesWithExposure g D 0).card : ℝ) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by simp
    _ ≤ ((4096 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)^4) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m 0 hD (by omega)
    _ = _ := by field_simp; ring

theorem lineHit_probabilitySum_le (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ T ∈ eligibleTuples g,
      conditionalProbability D a (successfulLineHit T g L)) ≤
        (32768 * (m + 1) ^ 4 : ℝ) := by
  rw [← Finset.sum_filter_add_sum_filter_not (eligibleTuples g)
    (fun T => (exposedTupleIndices T D).card = 0)]
  have hpos : (eligibleTuples g).filter
      (fun T => ¬ (exposedTupleIndices T D).card = 0) =
      (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T D).card) := by
    apply Finset.filter_congr
    intro T _
    omega
  rw [hpos]
  have hsecond : (∑ T ∈ (eligibleTuples g).filter
      (fun T => 0 < (exposedTupleIndices T D).card),
      conditionalProbability D a (successfulLineHit T g L)) ≤
        (16384 * (m + 1) ^ 4 : ℝ) := by
    apply le_trans _ (overlapProbabilitySum_le g D a m hD)
    exact Finset.sum_le_sum (fun T _ => lineHit_probability_le_success T g L D a)
  have hfirst := lineHit_sum_fresh_le g L D a m hD
  change (∑ T ∈ (eligibleTuples g).filter
    (fun T => (exposedTupleIndices T D).card = 0),
    conditionalProbability D a (successfulLineHit T g L)) ≤ _ at hfirst
  linarith

theorem success_sum_two_three_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m j : ℕ) (hD : D.card ≤ m) (hj : j = 2 ∨ j = 3) :
    (∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (successfulInDirection T g)) ≤
        (4096 * (m + 1) ^ 4 : ℝ) / Fintype.card F := by
  have hj4 : j ≤ 4 := by omega
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _T ∈ tuplesWithExposure g D j,
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨hgood, hjT⟩ := Finset.mem_filter.mp hT
      obtain ⟨hinj, hg⟩ := (Finset.mem_filter.mp hgood).2
      simpa only [hjT] using successful_probability_le T hinj g hg D a
    _ = ((tuplesWithExposure g D j).card : ℝ) *
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by simp
    _ ≤ ((4096 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ) ^ (4-j)) *
        (Fintype.card F : ℝ)⁻¹ ^ alignmentExponent j := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m j hD hj4
    _ = _ := by rcases hj with rfl | rfl <;> norm_num [alignmentExponent] <;> field_simp

theorem sum_targets_success_two_three_le (D : Finset (Direction F))
    (a : MergedPairs F) (m j : ℕ) (hD : D.card ≤ m) (hj : j = 2 ∨ j = 3) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (successfulInDirection T g)) ≤
        (8192 * (m + 1) ^ 4 : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hdir : (Fintype.card (Direction F) : ℝ) ≤ 2 * Fintype.card F := by
    have hn : 0 < Fintype.card F := Fintype.card_pos
    have hd : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
      simp only [Direction, Fintype.card_option]
      omega
    exact_mod_cast hd
  calc
    _ ≤ ∑ _g : Direction F, (4096 * (m + 1) ^ 4 : ℝ) / Fintype.card F :=
      Finset.sum_le_sum (fun g _ => success_sum_two_three_le g D a m j hD hj)
    _ = (Fintype.card (Direction F) : ℝ) *
        ((4096 * (m + 1) ^ 4 : ℝ) / Fintype.card F) := by simp
    _ ≤ (2 * Fintype.card F : ℝ) *
        ((4096 * (m + 1) ^ 4 : ℝ) / Fintype.card F) := by gcongr
    _ = _ := by field_simp; ring

theorem sum_targets_success_four_le (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 4,
      conditionalProbability D a (successfulInDirection T g)) ≤
        16 * (D.card : ℝ)^4 := by
  let code : FourTuple F → (Fin 4 → Direction F) × (Fin 4 → Bool) :=
    fun T => (T.generator,T.side)
  have hinj : Function.Injective code := by
    intro T U h
    cases T
    cases U
    cases h
    rfl
  have htarget (g : Direction F) :
      (∑ T ∈ tuplesWithExposure g D 4,
        conditionalProbability D a (successfulInDirection T g)) ≤
      ∑ c ∈ tupleCodesWithOldCount D 4,
        conditionalProbability D a (successfulInDirection ⟨c.1,c.2⟩ g) := by
    have hsub : (tuplesWithExposure g D 4).image code ⊆ tupleCodesWithOldCount D 4 := by
      intro c hc
      obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hc
      have hj := (Finset.mem_filter.mp hT).2
      simpa [code, tupleCodesWithOldCount, generatorLabelsWithOldCount,
        exposedTupleIndices] using hj
    calc
      _ = ∑ c ∈ (tuplesWithExposure g D 4).image code,
          conditionalProbability D a (successfulInDirection ⟨c.1,c.2⟩ g) := by
        rw [Finset.sum_image (fun T _ U _ h => hinj h)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ENNReal.toReal_nonneg)
  calc
    _ ≤ ∑ g : Direction F, ∑ c ∈ tupleCodesWithOldCount D 4,
        conditionalProbability D a (successfulInDirection ⟨c.1,c.2⟩ g) :=
      Finset.sum_le_sum (fun g _ => htarget g)
    _ = ∑ c ∈ tupleCodesWithOldCount D 4, ∑ g : Direction F,
        conditionalProbability D a (successfulInDirection ⟨c.1,c.2⟩ g) := Finset.sum_comm
    _ ≤ _ := sum_fully_exposed_code_success_probability_le D a

end
end Balanced.CandidateExposure

end OAI

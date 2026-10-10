import OAI.Combinatorics.BalancedRyser.Candidates.CandidateFirstMoment
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateLineGate
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateConditionalFreshIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.CandidatePartialPointIncidence

namespace OAI

namespace Balanced.CandidateGlobalLine

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def lineSuccessEvent (T : FourTuple F) (g : Direction F) (L : Line F) :
    Set (MergedPairs F) :=
  {M | M ∈ successfulInDirection T g ∧ ∃ i, OnLine (tuplePoint M T i) L}

theorem conditionalProbability_mono (D : Finset (Direction F)) (a : MergedPairs F)
    {E H : Set (MergedPairs F)} (h : E ⊆ H) :
    conditionalProbability D a E ≤ conditionalProbability D a H := by
  unfold conditionalProbability
  apply ENNReal.toReal_mono _ ((exposedLaw D a).toOuterMeasure.mono h)
  change (exposedLaw D a).toOuterMeasure H ≠ ⊤
  rw [PMF.toOuterMeasure_apply]
  exact (exposedLaw D a).tsum_coe_indicator_ne_top H

theorem lineSuccessEvent_probability_le (T : FourTuple F) (g : Direction F)
    (L : Line F) (D : Finset (Direction F)) (a : MergedPairs F) :
    conditionalProbability D a (lineSuccessEvent T g L) ≤
      conditionalProbability D a (successfulInDirection T g) :=
  conditionalProbability_mono D a (fun _ h => h.1)

theorem fresh_lineSuccessEvent_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hfresh : (exposedTupleIndices T D).card = 0) :
    conditionalProbability D a (lineSuccessEvent T g L) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  have hf : ∀ i, T.generator i ∉ D := by
    intro i hi
    have hempty := Finset.card_eq_zero.mp hfresh
    have hm : i ∈ exposedTupleIndices T D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    simp [hempty] at hm
  apply le_trans (conditionalProbability_mono D a (H :=
    {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, OnLine (tuplePoint M T i) L}) (fun _ h => ⟨h.1.1, h.2⟩))
  exact CandidateFreshIncidence.conditional_tuple_hits_line_probability_le
    T hT D a hf g L

theorem one_old_lineSuccessEvent_probability_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (g : Direction F)
    (hg : ∀ i, T.generator i ≠ g) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F)
    (hone : (exposedTupleIndices T D).card = 1)
    (ha : L ∉ constituentLines a) :
    conditionalProbability D a (lineSuccessEvent T g L) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  apply le_trans (conditionalProbability_mono D a (H :=
    {M | (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, OnLine (tuplePoint M T i) L}) (fun _ h => ⟨h.1.1, h.2⟩))
  exact CandidatePartialPointIncidence.conditional_tuple_hits_line_probability_le
    T hT D a hone.le g hg L (CandidateLineGate.exposed_constituents_avoid D a L ha)

theorem lineSuccess_sum_zero_one_le (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m j : ℕ)
    (hD : D.card ≤ m) (hj : j = 0 ∨ j = 1) (ha : L ∉ constituentLines a) :
    (∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (16384 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ j := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ _T ∈ tuplesWithExposure g D j, 4 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨helig, hexp⟩ := Finset.mem_filter.mp hT
      obtain ⟨hinj, htarget⟩ := (Finset.mem_filter.mp helig).2
      rcases hj with rfl | rfl
      · exact fresh_lineSuccessEvent_probability_le T hinj g L D a hexp
      · exact one_old_lineSuccessEvent_probability_le T hinj g htarget L D a hexp ha
    _ = ((tuplesWithExposure g D j).card : ℝ) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by simp
    _ ≤ ((4096 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ) ^ (4-j)) *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m j hD (by omega)
    _ = _ := by
      rcases hj with rfl | rfl <;> norm_num <;> field_simp <;> ring

theorem sum_targets_lineSuccess_zero_one_le (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m j : ℕ)
    (hD : D.card ≤ m) (hj : j = 0 ∨ j = 1) (ha : L ∉ constituentLines a) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (lineSuccessEvent T g L)) ≤
      (32768 * (m + 1) ^ 4 : ℝ) *
        (if j = 0 then (Fintype.card F : ℝ) else 1) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : (Fintype.card (Direction F) : ℝ) ≤ 2 * Fintype.card F := by
    have hn : 0 < Fintype.card F := Fintype.card_pos
    simp only [Direction, Fintype.card_option, Nat.cast_add, Nat.cast_one]
    have hp : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast hn
    linarith
  calc
    _ ≤ ∑ _g : Direction F,
        (16384 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ j :=
      Finset.sum_le_sum (fun g _ => lineSuccess_sum_zero_one_le g L D a m j hD hj ha)
    _ = (Fintype.card (Direction F) : ℝ) *
        ((16384 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ j) := by simp
    _ ≤ (2 * (Fintype.card F : ℝ)) *
        ((16384 * (m + 1) ^ 4 : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ j) := by
      exact mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := by
      rcases hj with rfl | rfl <;> norm_num <;> field_simp <;> ring

end
end Balanced.CandidateGlobalLine

end OAI

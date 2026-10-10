import OAI.Combinatorics.BalancedRyser.Candidates.CandidateFirstMoment
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateConditionalFreshIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.CandidatePartialPointIncidence
import OAI.Combinatorics.BalancedRyser.Probability.FullyExposedTargets

namespace OAI

namespace Balanced.CandidatePointIncidence

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def pointEvent (T : FourTuple F) (g : Direction F) (y : Point F) :
    Set (MergedPairs F) :=
  successfulInDirection T g ∩ {M | ∃ i, tuplePoint M T i = y}

def pointLineEvent (T : FourTuple F) (g : Direction F) (y : Point F) (K : Line F) :
    Set (MergedPairs F) :=
  {M | (∀ i, OnLine (tuplePoint M T i) (lineThrough g y)) ∧
    Function.Injective (tuplePoint M T) ∧ ∃ i, OnLine (tuplePoint M T i) K}

theorem conditionalProbability_mono (D : Finset (Direction F)) (a : MergedPairs F)
    {E H : Set (MergedPairs F)} (h : E ⊆ H) :
    conditionalProbability D a E ≤ conditionalProbability D a H := by
  apply ENNReal.toReal_mono _ ((exposedLaw D a).toOuterMeasure.mono h)
  change (exposedLaw D a).toOuterMeasure H ≠ ⊤
  rw [PMF.toOuterMeasure_apply]
  exact (exposedLaw D a).tsum_coe_indicator_ne_top H

omit [Fintype F] [DecidableEq F] in
theorem pointEvent_subset_success (T : FourTuple F) (g : Direction F) (y : Point F) :
    pointEvent T g y ⊆ successfulInDirection T g := fun _ h => h.1

omit [Fintype F] [DecidableEq F] in
theorem pointLineEvent_subset_success (T : FourTuple F) (g : Direction F)
    (y : Point F) (K : Line F) :
    pointLineEvent T g y K ⊆ successfulInDirection T g := by
  rintro M ⟨hon, hinj, _⟩
  exact ⟨⟨lineEval g y, hon⟩, hinj⟩

theorem point_probability_fresh_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (y : Point F) :
    conditionalProbability D a (pointEvent T g y) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 5 := by
  apply (conditionalProbability_mono D a (H := {M |
    (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, tuplePoint M T i = y}) (fun _ h => ⟨h.1.1, h.2⟩)).trans
  exact CandidateFreshIncidence.conditional_tuple_contains_point_probability_le
    T hT D a hfresh g y

theorem point_probability_one_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (y : Point F) :
    conditionalProbability D a (pointEvent T g y) ≤
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  apply (conditionalProbability_mono D a (H := {M |
    (∃ c, ∀ j, OnLine (tuplePoint M T j) (g,c)) ∧
      ∃ i, tuplePoint M T i = y}) (fun _ h => ⟨h.1.1, h.2⟩)).trans
  exact CandidatePartialPointIncidence.conditional_tuple_contains_point_probability_le
    T hT D a hD g hg y

theorem pointLine_probability_fresh_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hfresh : ∀ i, T.generator i ∉ D)
    (g : Direction F) (y : Point F) (K : Line F) (hyK : ¬ OnLine y K) :
    conditionalProbability D a (pointLineEvent T g y K) ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 5 := by
  apply (conditionalProbability_mono D a (H := {M |
    (∀ j, OnLine (tuplePoint M T j) (lineThrough g y)) ∧
      ∃ i, OnLine (tuplePoint M T i) K}) (fun _ h => ⟨h.1, h.2.2⟩)).trans
  exact CandidateFreshIncidence.conditional_tuple_through_point_hits_line_probability_le
    T hT D a hfresh g y K hyK

theorem pointLine_probability_one_le (T : FourTuple F)
    (hT : Function.Injective T.generator) (D : Finset (Direction F))
    (a : MergedPairs F) (hD : (exposedTupleIndices T D).card ≤ 1)
    (g : Direction F) (hg : ∀ i, T.generator i ≠ g) (y : Point F) (K : Line F) :
    conditionalProbability D a (pointLineEvent T g y K) ≤
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  apply (conditionalProbability_mono D a (H := {M |
    (∀ j, OnLine (tuplePoint M T j) (lineThrough g y)) ∧
      ∃ i, OnLine (tuplePoint M T i) K}) (fun _ h => ⟨h.1, h.2.2⟩)).trans
  exact CandidatePartialPointIncidence.conditional_tuple_through_point_hits_line_probability_le
    T hT D a hD g hg y K

theorem sum_stratum_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m j : ℕ) (hD : D.card ≤ m) (hj : j ≤ 4)
    (E : FourTuple F → Direction F → Set (MergedPairs F)) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ g T, T ∈ tuplesWithExposure g D j →
      conditionalProbability D a (E T g) ≤ C * (Fintype.card F : ℝ)⁻¹ ^ (5-j)) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (E T g)) ≤ 8192 * C * ((m : ℝ)+1)^4 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hdir : (Fintype.card (Direction F) : ℝ) ≤ 2 * Fintype.card F := by
    have hn : 0 < Fintype.card F := Fintype.card_pos
    have hd : Fintype.card (Direction F) ≤ 2 * Fintype.card F := by
      simp only [Direction, Fintype.card_option]
      omega
    exact_mod_cast hd
  have hexp : 5-j = (4-j)+1 := by omega
  calc
    _ ≤ ∑ g : Direction F, ((tuplesWithExposure g D j).card : ℝ) *
        (C * (Fintype.card F : ℝ)⁻¹ ^ (5-j)) := by
      apply Finset.sum_le_sum
      intro g _
      simpa using Finset.sum_le_sum (fun T hT => hE g T hT)
    _ ≤ ∑ _g : Direction F,
        ((4096 * ((m : ℝ)+1)^4) * (Fintype.card F : ℝ)^(4-j)) *
          (C * (Fintype.card F : ℝ)⁻¹ ^ (5-j)) := by
      apply Finset.sum_le_sum
      intro g _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tuplesWithExposure_le g D m j hD hj
    _ = (Fintype.card (Direction F) : ℝ) *
        (((4096 * ((m : ℝ)+1)^4) * (Fintype.card F : ℝ)^(4-j)) *
          (C * (Fintype.card F : ℝ)⁻¹ ^ (5-j))) := by simp
    _ ≤ (2 * (Fintype.card F : ℝ)) *
        (((4096 * ((m : ℝ)+1)^4) * (Fintype.card F : ℝ)^(4-j)) *
          (C * (Fintype.card F : ℝ)⁻¹ ^ (5-j))) := by gcongr
    _ = _ := by
      rw [hexp, pow_succ, inv_pow]
      field_simp
      ring

omit [Field F] [Fintype F] in
theorem fresh_of_exposure_zero (T : FourTuple F) (D : Finset (Direction F))
    (h : (exposedTupleIndices T D).card = 0) : ∀ i, T.generator i ∉ D := by
  have hz := Finset.card_eq_zero.mp h
  intro i hi
  have hm : i ∈ exposedTupleIndices T D := by simp [exposedTupleIndices, hi]
  rw [hz] at hm
  exact Finset.notMem_empty i hm

theorem point_sum_fresh_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 0,
      conditionalProbability D a (pointEvent T g y)) ≤
        32768 * ((m : ℝ)+1)^4 := by
  apply (sum_stratum_le D a m 0 hD (by omega)
    (fun T g => pointEvent T g y) 4 (by norm_num) ?_).trans_eq
  · ring
  · intro g T hT
    obtain ⟨he, hz⟩ := Finset.mem_filter.mp hT
    exact point_probability_fresh_le T (Finset.mem_filter.mp he).2.1 D a
      (fresh_of_exposure_zero T D hz) g y

theorem point_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 1,
      conditionalProbability D a (pointEvent T g y)) ≤
        8192 * ((m : ℝ)+1)^4 := by
  apply (sum_stratum_le D a m 1 hD (by omega)
    (fun T g => pointEvent T g y) 1 (by norm_num) ?_).trans_eq
  · ring
  · intro g T hT
    obtain ⟨he, hz⟩ := Finset.mem_filter.mp hT
    obtain ⟨hinj, hg⟩ := (Finset.mem_filter.mp he).2
    simpa using point_probability_one_le T hinj D a hz.le g hg y

theorem pointLine_sum_fresh_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) (K : Line F) (hyK : ¬ OnLine y K) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 0,
      conditionalProbability D a (pointLineEvent T g y K)) ≤
        32768 * ((m : ℝ)+1)^4 := by
  apply (sum_stratum_le D a m 0 hD (by omega)
    (fun T g => pointLineEvent T g y K) 4 (by norm_num) ?_).trans_eq
  · ring
  · intro g T hT
    obtain ⟨he, hz⟩ := Finset.mem_filter.mp hT
    exact pointLine_probability_fresh_le T (Finset.mem_filter.mp he).2.1 D a
      (fresh_of_exposure_zero T D hz) g y K hyK

theorem pointLine_sum_one_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) (K : Line F) :
    (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 1,
      conditionalProbability D a (pointLineEvent T g y K)) ≤
        8192 * ((m : ℝ)+1)^4 := by
  apply (sum_stratum_le D a m 1 hD (by omega)
    (fun T g => pointLineEvent T g y K) 1 (by norm_num) ?_).trans_eq
  · ring
  · intro g T hT
    obtain ⟨he, hz⟩ := Finset.mem_filter.mp hT
    obtain ⟨hinj, hg⟩ := (Finset.mem_filter.mp he).2
    simpa using pointLine_probability_one_le T hinj D a hz.le g hg y K

end
end Balanced.CandidatePointIncidence

end OAI

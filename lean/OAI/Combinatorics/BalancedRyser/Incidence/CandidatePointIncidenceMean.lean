import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceModel
import OAI.Combinatorics.BalancedRyser.Incidence.CandidatePointIncidence

namespace OAI

namespace Balanced.CandidatePointIncidence

noncomputable section
open scoped Classical BigOperators
open CandidateExposure PartialAlignment MeasureTheory

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem probabilitySum_eq_strata (D : Finset (Direction F)) (a : MergedPairs F)
    (E : FourTuple F → Direction F → Set (MergedPairs F)) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g, conditionalProbability D a (E T g)) =
      ∑ j ∈ Finset.range 5, ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (E T g) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := eligibleTuples g) (t := Finset.range 5)
    (g := fun T => (exposedTupleIndices T D).card)
    (fun T _ => Finset.mem_range.mpr (by
      have hc := (exposedTupleIndices T D).card_le_univ
      simp only [Fintype.card_fin] at hc
      omega)) (fun T => conditionalProbability D a (E T g))

theorem probabilitySum_le_of_low (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m)
    (E : FourTuple F → Direction F → Set (MergedPairs F))
    (hsub : ∀ T g, E T g ⊆ successfulInDirection T g)
    (hzero : (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 0,
      conditionalProbability D a (E T g)) ≤ 32768 * ((m : ℝ)+1)^4)
    (hone : (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D 1,
      conditionalProbability D a (E T g)) ≤ 8192 * ((m : ℝ)+1)^4) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g,
      conditionalProbability D a (E T g)) ≤ 60000 * ((m : ℝ)+1)^4 := by
  have hdom (j : ℕ) : (∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
      conditionalProbability D a (E T g)) ≤
      ∑ g : Direction F, ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (successfulInDirection T g) := by
    apply Finset.sum_le_sum
    intro g _
    exact Finset.sum_le_sum (fun T _ => conditionalProbability_mono D a (hsub T g))
  have htwo := (hdom 2).trans (sum_targets_success_two_three_le D a m 2 hD (Or.inl rfl))
  have hthree := (hdom 3).trans (sum_targets_success_two_three_le D a m 3 hD (Or.inr rfl))
  have hfour := (hdom 4).trans (sum_targets_success_four_le D a)
  have hc : (D.card : ℝ)^4 ≤ ((m : ℝ)+1)^4 := by
    gcongr
    exact (show (D.card : ℝ) ≤ ↑m from by exact_mod_cast hD).trans (by linarith)
  rw [probabilitySum_eq_strata]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ (m : ℝ)+1 by positivity) 4]

theorem point_probabilitySum_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g,
      conditionalProbability D a (pointEvent T g y)) ≤ 60000 * ((m : ℝ)+1)^4 :=
  probabilitySum_le_of_low D a m hD (fun T g => pointEvent T g y)
    (fun T g => pointEvent_subset_success T g y)
    (point_sum_fresh_le D a m hD y) (point_sum_one_le D a m hD y)

theorem pointLine_probabilitySum_le (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) (y : Point F) (K : Line F) (hyK : ¬ OnLine y K) :
    (∑ g : Direction F, ∑ T ∈ eligibleTuples g,
      conditionalProbability D a (pointLineEvent T g y K)) ≤ 60000 * ((m : ℝ)+1)^4 :=
  probabilitySum_le_of_low D a m hD (fun T g => pointLineEvent T g y K)
    (fun T g => pointLineEvent_subset_success T g y K)
    (pointLine_sum_fresh_le D a m hD y K hyK) (pointLine_sum_one_le D a m hD y K)

def pointTest (y : Point F) : CandidateIncidence.Test F := fun _ _ p => ∃ i, p i = y

def pointLineTest (y : Point F) (K : Line F) : CandidateIncidence.Test F :=
  fun _ g p => (∀ i, OnLine (p i) (lineThrough g y)) ∧ ∃ i, OnLine (p i) K

omit [Fintype F] [DecidableEq F] in
theorem pointLine_model_event_eq (T : FourTuple F) (g : Direction F)
    (y : Point F) (K : Line F) :
    {M | M ∈ successfulInDirection T g ∧ pointLineTest y K T g (tuplePoint M T)} =
      pointLineEvent T g y K := by
  ext M
  constructor
  · rintro ⟨hs, hon, hhit⟩
    exact ⟨hon, hs.2, hhit⟩
  · rintro ⟨hon, hinj, hhit⟩
    exact ⟨⟨⟨lineEval g y, hon⟩, hinj⟩, hon, hhit⟩

local instance pointIncidenceMeasurableSpace : MeasurableSpace F := ⊤

theorem point_model_fixed_count_le (y : Point F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (CandidateIncidence.allModel (pointTest y)).fixedExpectation D a
      (CandidateIncidence.allModel (pointTest y)).count ≤ 60000 * ((m : ℝ)+1)^4 := by
  rw [CandidateIncidence.allModel_fixed_count]
  exact point_probabilitySum_le D a m hD y

theorem pointLine_model_fixed_count_le (y : Point F) (K : Line F) (hyK : ¬ OnLine y K)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (CandidateIncidence.allModel (pointLineTest y K)).fixedExpectation D a
      (CandidateIncidence.allModel (pointLineTest y K)).count ≤ 60000 * ((m : ℝ)+1)^4 := by
  rw [CandidateIncidence.allModel_fixed_count]
  simp_rw [pointLine_model_event_eq]
  exact pointLine_probabilitySum_le D a m hD y K hyK

theorem point_model_moment_le (y : Point F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (CandidateIncidence.allModel (pointTest y)).fixedExpectation D a
      (fun M => (CandidateIncidence.allModel (pointTest y)).count M ^ s) ≤
      (60000 * ((m + (s-1)*4 : ℕ)+1)^4 : ℝ)^s := by
  apply (CandidateIncidence.allModel (pointTest y)).fixed_moment_le_pow D a 4 s _
    (by positivity) (fun b => (CandidateIncidence.allModel_support_card _ b).le)
  intro J hJ b
  exact point_model_fixed_count_le y (D ∪ J) b (m + (s-1)*4)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hD hJ))

theorem pointLine_model_moment_le (y : Point F) (K : Line F) (hyK : ¬ OnLine y K)
    (D : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (CandidateIncidence.allModel (pointLineTest y K)).fixedExpectation D a
      (fun M => (CandidateIncidence.allModel (pointLineTest y K)).count M ^ s) ≤
      (60000 * ((m + (s-1)*4 : ℕ)+1)^4 : ℝ)^s := by
  apply (CandidateIncidence.allModel (pointLineTest y K)).fixed_moment_le_pow D a 4 s _
    (by positivity) (fun b => (CandidateIncidence.allModel_support_card _ b).le)
  intro J hJ b
  exact pointLine_model_fixed_count_le y K hyK (D ∪ J) b (m + (s-1)*4)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hD hJ))

end
end Balanced.CandidatePointIncidence

end OAI

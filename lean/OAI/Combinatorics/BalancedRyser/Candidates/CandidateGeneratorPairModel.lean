import OAI.Combinatorics.BalancedRyser.Candidates.CandidateLabelBridge
import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePrescriptionTransport
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentModel

namespace OAI

namespace Balanced.CandidateGeneratorPair

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance : MeasurableSpace F := ⊤

abbrev patternModel (e : Finset (Direction F)) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := Σ g : Direction F, RootPrescription g
  support := fun a => generatorSet a.2.tuple
  event := fun a => {M | e ⊆ generatorSet a.2.tuple ∧ M ∈ rootSuccessEvent a.1 a.2}
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have heq := tuplePoint_eq_of_eq_on_generators a.2.tuple h
    simp only [Set.mem_ofPred_eq, rootSuccessEvent, heq]

theorem support_card (e : Finset (Direction F)) (a : (patternModel e).Label) :
    ((patternModel e).support a).card = 4 :=
  rootPatternModel_support_card a.1 a.2

def count (e : Finset (Direction F)) (M : MergedPairs F) : ℕ :=
  (CandidateRetentionTransport.successfulTest M
    (fun C => e ⊆ generatorSet C.tuple)).card

theorem patternModel_count (e : Finset (Direction F)) (M : MergedPairs F) :
    (patternModel e).count M = (count e M : ℝ) := by
  rw [count, CandidateRetentionTransport.successfulTest_card_eq_sum_prescriptions,
    Nat.cast_sum]
  unfold PatternModel.count
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  simp only [successfulPrescriptions, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  simp only [PatternModel.indicator, patternModel, Set.indicator_apply,
    Set.mem_ofPred_eq, rootSuccessEvent, RootPrescription.choice_tuple]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

theorem patternModel_measure (e : Finset (Direction F)) :
    (patternModel e).measure = (offsetLaw F).toMeasure := by
  exact rootPatternModel_measure (F := F) none

theorem fixedExpectation_exposed (e D : Finset (Direction F))
    (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (patternModel e).fixedExpectation D a f =
      ∫ M, f M ∂(exposedLaw D a).toMeasure := by
  exact rootPatternModel_fixedExpectation_exposed (F := F) none D a f

def probabilitySum (e D : Finset (Direction F)) (a : MergedPairs F) : ℝ :=
  ∑ g : Direction F, ∑ T ∈ (eligibleTuples g).filter
    (fun T => e ⊆ generatorSet T), conditionalProbability D a (successfulInDirection T g)

theorem count_eq_sum_eligible (e : Finset (Direction F)) (M : MergedPairs F) :
    count e M = ∑ g : Direction F,
      (((eligibleTuples g).filter (fun T => e ⊆ generatorSet T)).filter
        (fun T => M ∈ successfulInDirection T g)).card := by
  rw [count, CandidateRetentionTransport.successfulTest_card_eq_sum_prescriptions]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.card_bij (fun a _ => a.tuple)
  · intro a ha
    simp only [successfulPrescriptions, Finset.mem_filter] at ha
    obtain ⟨⟨_, hs⟩, he⟩ := ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨((eligibleTupleEquivRootPrescription g).symm a).2, he⟩, hs⟩
  · intro a _ b _ hab
    apply (eligibleTupleEquivRootPrescription g).symm.injective
    exact Subtype.ext hab
  · intro T hT
    obtain ⟨hT, hs⟩ := Finset.mem_filter.mp hT
    obtain ⟨hg, he⟩ := Finset.mem_filter.mp hT
    let a := eligibleTupleEquivRootPrescription g ⟨T, hg⟩
    have ha : a.tuple = T := equivRootPrescription_tuple g ⟨T, hg⟩
    refine ⟨a, ?_, ha⟩
    simp only [successfulPrescriptions, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · change M ∈ successfulInDirection a.tuple g
      simpa only [ha] using hs
    · change e ⊆ generatorSet a.tuple
      simpa only [ha] using he

theorem integral_count (e D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (count e M : ℝ) ∂(exposedLaw D a).toMeasure) = probabilitySum e D a := by
  simp_rw [count_eq_sum_eligible, Nat.cast_sum]
  rw [integral_finsetSum _ (fun g _ => Integrable.of_finite)]
  exact Finset.sum_congr rfl (fun g _ => integral_eventCount_eq_sum (exposedLaw D a)
    ((eligibleTuples g).filter (fun T => e ⊆ generatorSet T))
    (fun T => successfulInDirection T g))

omit [Field F] [Fintype F] in
theorem card_le_exposed_indices (e D : Finset (Direction F)) (T : FourTuple F)
    (heD : e ⊆ D) (heT : e ⊆ generatorSet T) :
    e.card ≤ (PartialAlignment.exposedTupleIndices T D).card := by
  have hsub : e ⊆ (PartialAlignment.exposedTupleIndices T D).image T.generator := by
    intro d hd
    obtain ⟨i, _, hdi⟩ := Finset.mem_image.mp (heT hd)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hdi ▸ heD hd⟩, hdi⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

theorem probabilitySum_le_exposure_strata (e D : Finset (Direction F))
    (a : MergedPairs F) (he : e.card = 2) (heD : e ⊆ D) :
    probabilitySum e D a ≤ ∑ j ∈ Finset.Icc 2 4, ∑ g : Direction F,
      ∑ T ∈ tuplesWithExposure g D j,
        conditionalProbability D a (successfulInDirection T g) := by
  rw [Finset.sum_comm]
  unfold probabilitySum
  apply Finset.sum_le_sum
  intro g _
  have hpartition := Finset.sum_fiberwise_eq_sum_filter (eligibleTuples g)
    (Finset.Icc 2 4) (fun T => (PartialAlignment.exposedTupleIndices T D).card)
    (fun T => conditionalProbability D a (successfulInDirection T g))
  change _ ≤ ∑ j ∈ Finset.Icc 2 4,
    ∑ T ∈ (eligibleTuples g).filter
      (fun T => (PartialAlignment.exposedTupleIndices T D).card = j),
      conditionalProbability D a (successfulInDirection T g)
  rw [hpartition]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    obtain ⟨hT, heT⟩ := Finset.mem_filter.mp hT
    apply Finset.mem_filter.mpr
    refine ⟨hT, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · simpa only [he] using card_le_exposed_indices e D T heD heT
    · simpa only [Fintype.card_fin] using
        (PartialAlignment.exposedTupleIndices T D).card_le_univ
  · intro T _ _
    exact ENNReal.toReal_nonneg

end
end Balanced.CandidateGeneratorPair

end OAI

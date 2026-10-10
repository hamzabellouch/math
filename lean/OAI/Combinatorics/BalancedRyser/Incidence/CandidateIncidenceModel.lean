import OAI.Combinatorics.BalancedRyser.Candidates.CandidateRootCount
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceMean
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentModel
import OAI.Combinatorics.BalancedRyser.Probability.RootPatternModel

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment CandidateExposure

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance incidenceModelMeasurableSpace : MeasurableSpace F := ⊤

abbrev Test (F : Type*) := FourTuple F → Direction F → (Fin 4 → Point F) → Prop

def event (R : Test F) (g : Direction F) (a : RootPrescription g) :
    Set (MergedPairs F) :=
  {M | M ∈ rootSuccessEvent g a ∧ R a.tuple g (tuplePoint M a.tuple)}

abbrev model (R : Test F) (g : Direction F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := RootPrescription g
  support := fun a => generatorSet a.tuple
  event := event R g
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have heq := tuplePoint_eq_of_eq_on_generators a.tuple h
    simp only [event, rootSuccessEvent, Set.mem_ofPred_eq, heq]

abbrev allModel (R : Test F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := Σ g : Direction F, RootPrescription g
  support := fun a => generatorSet a.2.tuple
  event := fun a => event R a.1 a.2
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have heq := tuplePoint_eq_of_eq_on_generators a.2.tuple h
    simp only [event, rootSuccessEvent, Set.mem_ofPred_eq, heq]

theorem model_support_card (R : Test F) (g : Direction F) (a : RootPrescription g) :
    ((model R g).support a).card = 4 := rootPatternModel_support_card g a

theorem allModel_support_card (R : Test F) (a : (allModel R).Label) :
    ((allModel R).support a).card = 4 := rootPatternModel_support_card a.1 a.2

def tupleCount (R : Test F) (g : Direction F) (M : MergedPairs F) : ℕ :=
  ((eligibleTuples g).filter fun T =>
    M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)).card

theorem model_count (R : Test F) (g : Direction F) (M : MergedPairs F) :
    (model R g).count M = (tupleCount R g M : ℝ) := by
  have hc : (Finset.univ.filter (fun a : RootPrescription g => M ∈ event R g a)).card =
      tupleCount R g M := by
    apply Finset.card_bij (fun a _ => a.tuple)
    · intro a ha
      obtain ⟨_, hs⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨((eligibleTupleEquivRootPrescription g).symm a).2,hs⟩
    · intro a _ b _ hab
      apply (eligibleTupleEquivRootPrescription g).symm.injective
      exact Subtype.ext hab
    · intro T hT
      obtain ⟨hg,hs⟩ := Finset.mem_filter.mp hT
      let a := eligibleTupleEquivRootPrescription g ⟨T,hg⟩
      have ha : a.tuple = T := equivRootPrescription_tuple g ⟨T,hg⟩
      refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,ha⟩
      change M ∈ successfulInDirection a.tuple g ∧ R a.tuple g (tuplePoint M a.tuple)
      simpa only [ha] using hs
  rw [← hc]
  simp only [PatternModel.count, PatternModel.indicator, model,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_filter, Set.indicator_apply]

theorem allModel_count (R : Test F) (M : MergedPairs F) :
    (allModel R).count M = ∑ g : Direction F, (tupleCount R g M : ℝ) := by
  change (∑ a : Σ g : Direction F, RootPrescription g,
    (event R a.1 a.2).indicator (fun _ => (1 : ℝ)) M) = _
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun g _ => model_count R g M)

theorem model_measure (R : Test F) (g : Direction F) :
    (model R g).measure = (offsetLaw F).toMeasure := rootPatternModel_measure g

theorem allModel_measure (R : Test F) :
    (allModel R).measure = (offsetLaw F).toMeasure := rootPatternModel_measure (none : Direction F)

theorem model_fixedExpectation (R : Test F) (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (model R g).fixedExpectation D a f = ∫ M, f M ∂(exposedLaw D a).toMeasure :=
  rootPatternModel_fixedExpectation_exposed g D a f

theorem allModel_fixedExpectation (R : Test F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (allModel R).fixedExpectation D a f = ∫ M, f M ∂(exposedLaw D a).toMeasure :=
  rootPatternModel_fixedExpectation_exposed (none : Direction F) D a f

theorem model_fixed_count (R : Test F) (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (model R g).fixedExpectation D a (model R g).count =
      ∑ T ∈ eligibleTuples g, conditionalProbability D a
        {M | M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)} := by
  rw [model_fixedExpectation]
  simp_rw [model_count]
  simpa only [tupleCount, conditionalProbability, Set.mem_ofPred_eq] using
    integral_eventCount_eq_sum (exposedLaw D a) (eligibleTuples g)
      (fun T => {M | M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)})

theorem allModel_fixed_count (R : Test F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (allModel R).fixedExpectation D a (allModel R).count =
      ∑ g : Direction F, ∑ T ∈ eligibleTuples g, conditionalProbability D a
        {M | M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)} := by
  rw [allModel_fixedExpectation]
  simp_rw [allModel_count]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro g _
  simpa only [tupleCount, conditionalProbability, Set.mem_ofPred_eq] using
    integral_eventCount_eq_sum (exposedLaw D a) (eligibleTuples g)
      (fun T => {M | M ∈ successfulInDirection T g ∧ R T g (tuplePoint M T)})

def overlapTest (R : Test F) (K₀ K : Finset (Direction F)) : Test F :=
  fun T g p => ¬ Disjoint (generatorSet T \ K₀) K ∧ R T g p

theorem model_overlapCount (R : Test F) (g : Direction F)
    (K₀ K : Finset (Direction F)) (M : MergedPairs F) :
    (model R g).overlapCount K₀ K M =
      (model (overlapTest R K₀ K) g).count M := by
  unfold PatternModel.overlapCount PatternModel.count
  apply Finset.sum_congr rfl
  intro a _
  simp only [PatternModel.indicator, model, event, overlapTest, Set.indicator_apply,
    Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem allModel_overlapCount (R : Test F)
    (K₀ K : Finset (Direction F)) (M : MergedPairs F) :
    (allModel R).overlapCount K₀ K M =
      (allModel (overlapTest R K₀ K)).count M := by
  unfold PatternModel.overlapCount PatternModel.count
  apply Finset.sum_congr rfl
  intro a _
  simp only [PatternModel.indicator, allModel, event, overlapTest, Set.indicator_apply,
    Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem allModel_fixed_overlapCount (R : Test F)
    (K₀ K D : Finset (Direction F)) (a : MergedPairs F) :
    (allModel R).fixedExpectation D a ((allModel R).overlapCount K₀ K) =
      ∑ g : Direction F, ∑ T ∈ eligibleTuples g, conditionalProbability D a
        {M | M ∈ successfulInDirection T g ∧
          ¬ Disjoint (generatorSet T \ K₀) K ∧ R T g (tuplePoint M T)} := by
  have heq : (allModel R).overlapCount K₀ K =
      (allModel (overlapTest R K₀ K)).count := by
    funext M
    exact allModel_overlapCount R K₀ K M
  rw [heq]
  exact allModel_fixed_count (overlapTest R K₀ K) D a

def lineHitTest (L : Line F) : Test F := fun _ _ p => ∃ i, OnLine (p i) L

theorem lineHit_model_fixed_count_le (g : Direction F) (L : Line F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (model (lineHitTest L) g).fixedExpectation D a (model (lineHitTest L) g).count ≤
      (32768 * (m + 1)^4 : ℝ) := by
  rw [model_fixed_count]
  exact lineHit_probabilitySum_le g L D a m hD

theorem lineHit_model_moment_le (g : Direction F) (L : Line F)
    (K₀ : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hK : K₀.card ≤ m) :
    (model (lineHitTest L) g).fixedExpectation K₀ a
      (fun M => (model (lineHitTest L) g).count M ^ s) ≤
        (32768 * ((m + (s-1)*4 : ℕ) + 1)^4 : ℝ)^s := by
  apply (model (lineHitTest L) g).fixed_moment_le_pow K₀ a 4 s _ (by positivity)
    (fun b => (model_support_card _ _ b).le)
  intro K hK' y
  exact lineHit_model_fixed_count_le g L (K₀ ∪ K) y (m + (s-1)*4)
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hK hK'))

end
end Balanced.CandidateIncidence

end OAI

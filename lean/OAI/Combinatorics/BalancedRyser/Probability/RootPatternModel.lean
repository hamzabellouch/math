import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConditionalMean
import OAI.Combinatorics.BalancedRyser.Probability.FiniteFixedLaw
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentsLemmas
import OAI.Combinatorics.BalancedRyser.Probability.RootSuccess

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Balanced.TupleAlignment

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

local instance : MeasurableSpace F := ⊤

def rootSuccessEvent (g : Direction F) (a : RootPrescription g) :
    Set (MergedPairs F) :=
  {M | (∃ c, ∀ i, OnLine (tuplePoint M a.tuple i) (g, c)) ∧
    Function.Injective (tuplePoint M a.tuple)}

omit [Fintype F] in
theorem tuplePoint_eq_of_eq_on_generators (T : FourTuple F)
    {M N : MergedPairs F}
    (h : ∀ d ∈ generatorSet T, M d = N d) :
    tuplePoint M T = tuplePoint N T := by
  funext i
  have h₁ := h (T.generator i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have h₂ := h (T.generator (i + 1))
    (Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩)
  simp only [tuplePoint, constituent, h₁, h₂]

abbrev rootPatternModel (g : Direction F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := RootPrescription g
  support := fun a => generatorSet a.tuple
  event := rootSuccessEvent g
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := by
    intro a M N h
    have heq := tuplePoint_eq_of_eq_on_generators a.tuple h
    simp only [rootSuccessEvent, Set.mem_ofPred_eq, heq]

theorem rootPatternModel_support_card (g : Direction F) (a : RootPrescription g) :
    ((rootPatternModel g).support a).card = 4 := by
  exact (Finset.card_image_of_injective _ a.injective).trans (by simp)

theorem rootPatternModel_count (g : Direction F) (M : MergedPairs F) :
    (rootPatternModel g).count M = (rootSuccessCount g M : ℝ) := by
  simp only [PatternModel.count, PatternModel.indicator, rootPatternModel,
    rootSuccessEvent, rootSuccessCount, Set.indicator_apply,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_filter, Set.mem_ofPred_eq]

def rootOverlapCount (g : Direction F) (K₀ K : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  (Finset.univ.filter fun a : RootPrescription g =>
    ¬ Disjoint (generatorSet a.tuple \ K₀) K ∧ M ∈ rootSuccessEvent g a).card

theorem rootPatternModel_overlapCount (g : Direction F)
    (K₀ K : Finset (Direction F)) (M : MergedPairs F) :
    (rootPatternModel g).overlapCount K₀ K M =
      (rootOverlapCount g K₀ K M : ℝ) := by
  simp only [PatternModel.overlapCount, PatternModel.indicator, rootPatternModel,
    rootOverlapCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

theorem rootPatternModel_measure (g : Direction F) :
    (rootPatternModel g).measure = (offsetLaw F).toMeasure := by
  change Measure.pi (fun _ : Direction F =>
    (PMF.uniformOfFintype (Bool → F)).toMeasure) = (offsetLaw F).toMeasure
  apply Measure.ext_of_singleton
  intro M
  simp only [Measure.pi_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, offsetLaw, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    MergedPairs, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

theorem rootPatternModel_integral (g : Direction F) (f : MergedPairs F → ℝ) :
    (∫ M, f M ∂(rootPatternModel g).measure) =
      (∑ M, f M) / Fintype.card (MergedPairs F) := by
  rw [rootPatternModel_measure]
  change (∫ M : MergedPairs F, f M ∂(offsetLaw F).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp only [offsetLaw, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv]
  simp only [Fintype.card_eq_nat_card]
  rw [mul_comm]

theorem rootPatternModel_fixedExpectation (g : Direction F)
    (K : Finset (Direction F)) (x : MergedPairs F) (f : MergedPairs F → ℝ) :
    (rootPatternModel g).fixedExpectation K x f =
      (∑ M : MergedPairs F, f (fun d => if d ∈ K then x d else M d)) /
        Fintype.card (MergedPairs F) := by
  exact rootPatternModel_integral g
    (fun M => f (fun d => if d ∈ K then x d else M d))

theorem rootPatternModel_fixed_count (g : Direction F)
    (K : Finset (Direction F)) (x : MergedPairs F) :
    (rootPatternModel g).fixedExpectation K x (rootPatternModel g).count =
      (∑ M : MergedPairs F,
        (rootSuccessCount g (fun d => if d ∈ K then x d else M d) : ℝ)) /
        Fintype.card (MergedPairs F) := by
  rw [rootPatternModel_fixedExpectation]
  simp_rw [rootPatternModel_count]

theorem rootPatternModel_fixedExpectation_exposed (g : Direction F)
    (K : Finset (Direction F)) (x : MergedPairs F) (f : MergedPairs F → ℝ) :
    (rootPatternModel g).fixedExpectation K x f =
      ∫ M, f M ∂(CandidateExposure.exposedLaw K x).toMeasure := by
  have h := ConditionalRestriction.integral_fixArray_eq_filtered
    (fun d => d ∈ K) x f
  simp only [CandidateExposure.exposedLaw, PartialAlignment.offsetLaw_eq_uniform]
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with M
  congr 1
  funext d
  simp only [PatternModel.fixCoordinates, ConditionalRestriction.fixArray]
  split_ifs <;> rfl

theorem rootPatternModel_fixed_overlapCount (g : Direction F)
    (K₀ K L : Finset (Direction F)) (x : MergedPairs F) :
    (rootPatternModel g).fixedExpectation L x
        ((rootPatternModel g).overlapCount K₀ K) =
      ∫ M, (rootOverlapCount g K₀ K M : ℝ)
        ∂(CandidateExposure.exposedLaw L x).toMeasure := by
  rw [rootPatternModel_fixedExpectation_exposed]
  simp_rw [rootPatternModel_overlapCount]

theorem rootPatternModel_fixed_count_exposed (g : Direction F)
    (K : Finset (Direction F)) (x : MergedPairs F) :
    (rootPatternModel g).fixedExpectation K x (rootPatternModel g).count =
      ∫ M, (rootSuccessCount g M : ℝ)
        ∂(CandidateExposure.exposedLaw K x).toMeasure := by
  rw [rootPatternModel_fixedExpectation_exposed]
  simp_rw [rootPatternModel_count]

end Balanced.TupleAlignment

end

end OAI

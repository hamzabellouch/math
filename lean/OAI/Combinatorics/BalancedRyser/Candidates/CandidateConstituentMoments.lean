import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConstituentTarget
import OAI.Combinatorics.BalancedRyser.Probability.FiniteFixedLaw
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentModel

namespace OAI

namespace Balanced.CandidatePrescribed

noncomputable section
open scoped Classical BigOperators
open MeasureTheory ConditionalRestriction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local instance : MeasurableSpace F := ⊤
local instance : MeasurableSingletonClass F := ⟨fun _ => trivial⟩

theorem constituentTarget_mem_iff_of_agree (g : Direction F) (c : Code F)
    (M N : MergedPairs F)
    (h : ∀ d ∈ insert g (generatorSet (⟨c.1,c.2⟩ : FourTuple F)), M d = N d) :
    c ∈ constituentTargetCodes M g ↔ c ∈ constituentTargetCodes N g := by
  have hg : M g = N g := h g (Finset.mem_insert_self _ _)
  have hp : tuplePoint M (⟨c.1,c.2⟩ : FourTuple F) =
      tuplePoint N (⟨c.1,c.2⟩ : FourTuple F) := by
    funext i
    have hi := h (c.1 i) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hn := h (c.1 (i+1)) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i+1, Finset.mem_univ _, rfl⟩))
    simp only [tuplePoint, constituent, hi, hn]
  simp only [constituentTargetCodes, Finset.mem_union, successfulCodes,
    alignedCodes, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [constituent, hg, hp]

def constituentTargetPatternModel (g : Direction F) : PatternModel where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := Code F
  support c := insert g (generatorSet (⟨c.1,c.2⟩ : FourTuple F))
  event c := {M | c ∈ constituentTargetCodes M g}
  eventMeasurable _ := (Set.to_countable _).measurableSet
  dependsOn c M N h := constituentTarget_mem_iff_of_agree g c M N h

theorem constituentTargetPatternModel_support_card (g : Direction F) (c : Code F) :
    ((constituentTargetPatternModel g).support c).card ≤ 5 := by
  change (insert g (generatorSet (⟨c.1,c.2⟩ : FourTuple F))).card ≤ 5
  have hi := Finset.card_insert_le g (generatorSet (⟨c.1,c.2⟩ : FourTuple F))
  have hg : (generatorSet (⟨c.1,c.2⟩ : FourTuple F)).card ≤ 4 := by
    exact (Finset.card_image_le).trans (by simp)
  omega

theorem constituentTargetPatternModel_count (g : Direction F) (M : MergedPairs F) :
    (constituentTargetPatternModel g).count M =
      ((constituentTargetCodes M g).card : ℝ) := by
  simp only [PatternModel.count, PatternModel.indicator,
    constituentTargetPatternModel, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [← Finset.sum_filter]
  erw [Finset.filter_mem_eq_of_subset (Finset.subset_univ _)]
  simp

theorem constituentTargetPatternModel_fixedExpectation (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (constituentTargetPatternModel g).fixedExpectation old a f =
      ∑ M : MergedPairs F, (exposedLaw old a M).toReal * f M := by
  have hfix : (constituentTargetPatternModel g).fixCoordinates old a =
      fixArray (fun d => d ∈ old) a := by
    funext M d
    simp only [PatternModel.fixCoordinates, fixArray]
    congr 1
  unfold PatternModel.fixedExpectation
  rw [hfix]
  change (∫ M, f (fixArray (fun d => d ∈ old) a M) ∂Measure.pi
    (fun _ : Direction F => (PMF.uniformOfFintype (Bool → F)).toMeasure)) = _
  rw [integral_fixArray_eq_filtered]
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  congr 1
  funext M
  congr 2
  simp only [exposedLaw, PartialAlignment.offsetLaw_eq_uniform]

theorem constituentTarget_fixed_count_le_of_mem (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (hg : g ∈ old) :
    (constituentTargetPatternModel g).fixedExpectation old a
      (constituentTargetPatternModel g).count ≤
        40960 * ((old.card : ℝ) + 1) ^ 4 := by
  erw [constituentTargetPatternModel_fixedExpectation]
  simp_rw [constituentTargetPatternModel_count]
  exact expected_constituentTargetCodes_le old a g hg

theorem constituentTarget_count_measurable (g : Direction F) :
    Measurable (constituentTargetPatternModel g).count := by
  change Measurable (fun M : MergedPairs F => (constituentTargetPatternModel g).count M)
  exact measurable_of_countable _

theorem constituentTarget_count_nonneg (g : Direction F) (M : MergedPairs F) :
    0 ≤ (constituentTargetPatternModel g).count M := by
  rw [constituentTargetPatternModel_count]
  positivity

theorem constituentTarget_count_le_card (g : Direction F) (M : MergedPairs F) :
    (constituentTargetPatternModel g).count M ≤ Fintype.card (Code F) := by
  rw [constituentTargetPatternModel_count]
  exact_mod_cast Finset.card_le_univ (constituentTargetCodes M g)

theorem constituentTarget_fixed_count_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) :
    (constituentTargetPatternModel g).fixedExpectation old a
      (constituentTargetPatternModel g).count ≤
        40960 * ((old.card : ℝ) + 2) ^ 4 := by
  let P := constituentTargetPatternModel g
  have hbound (y : P.Sample) : P.fixedExpectation (old ∪ {g}) y P.count ≤
      40960 * ((old.card : ℝ) + 2) ^ 4 := by
    have h := constituentTarget_fixed_count_le_of_mem g (old ∪ {g}) y (by simp)
    apply h.trans
    have hcard : ((old ∪ {g}).card : ℝ) ≤ (old.card : ℝ) + 1 := by
      exact_mod_cast (show (old ∪ {g}).card ≤ old.card + 1 by
        simpa using Finset.card_union_le old {g})
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have h := P.fixedExpectation_mul_le_of_fixedBounds old {g} a
    (fun _ => 1) P.count (40960 * ((old.card : ℝ) + 2) ^ 4)
    1 (Fintype.card (Code F)) (by positivity)
    measurable_const (constituentTarget_count_measurable g)
    (fun _ => zero_le_one) (constituentTarget_count_nonneg g)
    (fun _ => le_rfl) (constituentTarget_count_le_card g)
    (by intros; rfl) hbound
  simpa [PatternModel.fixedExpectation, PatternModel.measure] using h

theorem constituentTarget_moment_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (s : ℕ) :
    (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
      ((constituentTargetCodes M g).card : ℝ) ^ s) ≤
      (40960 * (((old.card + (s - 1) * 5 : ℕ) : ℝ) + 2) ^ 4) ^ s := by
  let P := constituentTargetPatternModel g
  have hbound (K : Finset P.Color) (hK : K.card ≤ (s - 1) * 5)
      (y : P.Sample) : P.fixedExpectation (old ∪ K) y P.count ≤
        40960 * (((old.card + (s - 1) * 5 : ℕ) : ℝ) + 2) ^ 4 := by
    apply (constituentTarget_fixed_count_le g (old ∪ K) y).trans
    have hc : (old ∪ K).card ≤ old.card + (s - 1) * 5 :=
      (Finset.card_union_le old K).trans (Nat.add_le_add_left hK _)
    gcongr
  have h := P.fixed_moment_le_pow old a 5 s
    (40960 * (((old.card + (s - 1) * 5 : ℕ) : ℝ) + 2) ^ 4)
    (by positivity) (constituentTargetPatternModel_support_card g) hbound
  erw [constituentTargetPatternModel_fixedExpectation] at h
  simpa only [P, constituentTargetPatternModel_count] using h

theorem constituentTarget_moment_le_of_card_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ)
    (hm : old.card ≤ m) :
    (∑ M : MergedPairs F, (exposedLaw old a M).toReal *
      ((constituentTargetCodes M g).card : ℝ) ^ s) ≤
      (40960 * (((m + (s - 1) * 5 : ℕ) : ℝ) + 2) ^ 4) ^ s := by
  apply (constituentTarget_moment_le g old a s).trans
  gcongr

theorem constituentTarget_fixed_moment_le_of_card_le (g : Direction F)
    (old : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ)
    (hm : old.card ≤ m) :
    (constituentTargetPatternModel g).fixedExpectation old a
      (fun M => (constituentTargetPatternModel g).count M ^ s) ≤
      (40960 * (((m + (s - 1) * 5 : ℕ) : ℝ) + 2) ^ 4) ^ s := by
  erw [constituentTargetPatternModel_fixedExpectation]
  simp_rw [constituentTargetPatternModel_count]
  exact constituentTarget_moment_le_of_card_le g old a m s hm

end
end Balanced.CandidatePrescribed

end OAI

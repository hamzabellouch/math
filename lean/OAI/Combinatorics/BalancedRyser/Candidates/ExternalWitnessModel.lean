import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityWitness
import OAI.Combinatorics.BalancedRyser.Probability.RootPatternModel

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateValidityWitness
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance externalModelMeasurableSpace : MeasurableSpace F := ⊤

abbrev WitnessKey (F : Type u) :=
  (FourTuple F × (Fin 4 × Fin 4)) × (Direction F × Direction F)

def targetLine (g : Direction F) (M : MergedPairs F) (T : FourTuple F) : Line F :=
  (g, lineEval g (tuplePoint M T 0))

omit [Fintype F] [DecidableEq F] in
theorem targetLine_eq_of_success {M : MergedPairs F} {T : FourTuple F}
    {S : Line F} (h : SuccessfulOn M T S) : targetLine S.1 M T = S := by
  apply Prod.ext
  · rfl
  · exact h.2.2.2 0

def witnessEvent (g : Direction F) (w : WitnessKey F) : Set (MergedPairs F) :=
  {M | SuccessfulOn M w.1.1 (targetLine g M w.1.1) ∧
    w.1.2.1 ≠ w.1.2.2 ∧ w.2.1 ≠ w.2.2 ∧
    w.2.1 ≠ g ∧ w.2.2 ≠ g ∧
    w.2.1 ∉ generatorSet w.1.1 ∧ w.2.2 ∉ generatorSet w.1.1 ∧
    ∃ x, OnLine x (targetLine g M w.1.1) ∧
      x ∉ designated M ⟨targetLine g M w.1.1, w.1.1⟩ ∧
      PairWitness M w.2.1 x (tuplePoint M w.1.1 w.1.2.1) ∧
      PairWitness M w.2.2 x (tuplePoint M w.1.1 w.1.2.2)}

def witnesses (g : Direction F) (M : MergedPairs F) : Finset (WitnessKey F) :=
  Finset.univ.filter (fun w => M ∈ witnessEvent g w)

@[simp] theorem mem_witnesses (g : Direction F) (M : MergedPairs F)
    (w : WitnessKey F) : w ∈ witnesses g M ↔ M ∈ witnessEvent g w := by
  simp [witnesses]

theorem exists_witness_iff (g : Direction F) (M : MergedPairs F) (T : FourTuple F) :
    (∃ ij : Fin 4 × Fin 4, ∃ de : Direction F × Direction F,
      ((T, ij), de) ∈ witnesses g M) ↔
    SuccessfulOn M T (targetLine g M T) ∧
      ExternalDoubleWitness M T (targetLine g M T) := by
  constructor
  · rintro ⟨⟨i,j⟩, ⟨d,e⟩, hw⟩
    obtain ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩ :=
      (mem_witnesses g M _).mp hw
    exact ⟨hs, x, i, j, d, e, hx, hex, hij, hde, hd, he, hdT, heT, hdi, hej⟩
  · rintro ⟨hs, x, i, j, d, e, hx, hex, hij, hde, hd, he, hdT, heT, hdi, hej⟩
    exact ⟨(i,j), (d,e), (mem_witnesses g M _).mpr
      ⟨hs, hij, hde, hd, he, hdT, heT, x, hx, hex, hdi, hej⟩⟩

theorem image_witnesses (g : Direction F) (M : MergedPairs F) :
    (witnesses g M).image (fun w => w.1.1) =
      Finset.univ.filter (fun T => SuccessfulOn M T (targetLine g M T) ∧
        ExternalDoubleWitness M T (targetLine g M T)) := by
  ext T
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨⟨U, ij⟩, de⟩, hw, heq⟩
    change U = T at heq
    subst U
    exact (exists_witness_iff g M T).mp ⟨ij, de, hw⟩
  · intro hT
    obtain ⟨ij, de, hw⟩ := (exists_witness_iff g M T).mpr hT
    exact ⟨((T,ij),de), hw, rfl⟩

theorem failure_card_le (g : Direction F) (M : MergedPairs F) :
    (Finset.univ.filter (fun T => SuccessfulOn M T (targetLine g M T) ∧
      ExternalDoubleWitness M T (targetLine g M T))).card ≤ (witnesses g M).card := by
  rw [← image_witnesses]
  exact Finset.card_image_le

def support (w : WitnessKey F) : Finset (Direction F) :=
  generatorSet w.1.1 ∪ {w.2.1, w.2.2}

omit [Field F] [Fintype F] in
theorem support_card_le (w : WitnessKey F) : (support w).card ≤ 6 := by
  have hT : (generatorSet w.1.1).card ≤ 4 := by
    simpa [generatorSet] using
      (Finset.card_image_le (s := Finset.univ) (f := w.1.1.generator))
  have he : ({w.2.1,w.2.2} : Finset (Direction F)).card ≤ 2 :=
    by simpa using (Finset.card_insert_le w.2.1 ({w.2.2} : Finset (Direction F)))
  exact (Finset.card_union_le _ _).trans (by omega)

omit [Fintype F] in

theorem witnessEvent_congr (g : Direction F) (w : WitnessKey F)
    (M N : MergedPairs F) (h : ∀ d ∈ support w, M d = N d) :
    M ∈ witnessEvent g w ↔ N ∈ witnessEvent g w := by
  have hp := TupleAlignment.tuplePoint_eq_of_eq_on_generators w.1.1
    (fun d hd => h d (Finset.mem_union_left _ hd))
  have hd := h w.2.1 (Finset.mem_union_right _ (by simp))
  have he := h w.2.2 (Finset.mem_union_right _ (by simp))
  simp only [witnessEvent, Set.mem_ofPred_eq, SuccessfulOn, targetLine,
    designated, PairWitness, constituent, hp, hd, he]

abbrev patternModel (g : Direction F) : PatternModel.{u} where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := WitnessKey F
  support := support
  event := witnessEvent g
  eventMeasurable := fun _ => (Set.toFinite _).measurableSet
  dependsOn := witnessEvent_congr g

theorem patternModel_count (g : Direction F) (M : MergedPairs F) :
    (patternModel g).count M = ((witnesses g M).card : ℝ) := by
  simp only [PatternModel.count, PatternModel.indicator, patternModel,
    witnesses, Set.indicator_apply, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem patternModel_support_card_le (g : Direction F) (w : WitnessKey F) :
    ((patternModel g).support w).card ≤ 6 := support_card_le w

theorem patternModel_measure (g : Direction F) :
    (patternModel g).measure = (offsetLaw F).toMeasure :=
  TupleAlignment.rootPatternModel_measure g

theorem patternModel_fixedExpectation_exposed (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (patternModel g).fixedExpectation D a f =
      ∫ M, f M ∂(CandidateExposure.exposedLaw D a).toMeasure :=
  TupleAlignment.rootPatternModel_fixedExpectation_exposed g D a f

theorem patternModel_overlapCount (g : Direction F)
    (K₀ K : Finset (Direction F)) (M : MergedPairs F) :
    (patternModel g).overlapCount K₀ K M =
      (((witnesses g M).filter (fun w => ¬ Disjoint (support w \ K₀) K)).card : ℝ) := by
  simp only [PatternModel.overlapCount, PatternModel.indicator, patternModel,
    witnesses, Finset.filter_filter, Set.indicator_apply,
    Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp_all

theorem integral_count_eq_sum (g : Direction F) (law : PMF (MergedPairs F)) :
    (∫ M, ((witnesses g M).card : ℝ) ∂law.toMeasure) =
      ∑ w : WitnessKey F, (law.toOuterMeasure (witnessEvent g w)).toReal :=
  CandidateExposure.integral_eventCount_eq_sum law Finset.univ (witnessEvent g)

theorem fixed_count_eq_sum (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) :
    (patternModel g).fixedExpectation D a (patternModel g).count =
      ∑ w : WitnessKey F,
        ((CandidateExposure.exposedLaw D a).toOuterMeasure (witnessEvent g w)).toReal := by
  rw [patternModel_fixedExpectation_exposed]
  simp_rw [patternModel_count]
  exact integral_count_eq_sum g _

end
end Balanced.ExternalAssembly

end OAI

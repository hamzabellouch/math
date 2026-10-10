import OAI.Combinatorics.BalancedRyser.Candidates.CandidateMixedExternal
import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessModel

namespace OAI

namespace Balanced.CandidateMixedExternal

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateValidityWitness ExternalAssembly
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance mixedAssemblyMeasurableSpace : MeasurableSpace F := ⊤

def mixedOverlapFilter (D : Finset (Direction F)) (w : WitnessKey F) : Prop :=
  0 < (PartialAlignment.exposedTupleIndices w.1.1 D).card ∧
    w.2.1 ∈ D ∧ w.2.2 ∉ D

def mixedOverlapCount (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) : ℕ :=
  ((witnesses g M).filter (mixedOverlapFilter D)).card

def mixedOverlapKeys (g : Direction F) (D : Finset (Direction F)) :
    Finset (WitnessKey F) :=
  Finset.univ.filter fun w =>
    w.1.1 ∈ (eligibleTuples g).filter
      (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card) ∧
    w.2.1 ∈ oldWitnessDirections g w.1.1 D ∧
    w.2.2 ∈ freshWitnessDirections g w.1.1 D

theorem witnessEvent_eq_mixedExternalEvent
    (g : Direction F) (D : Finset (Direction F)) (T : FourTuple F)
    (d e : Direction F) (i j : Fin 4) (hT : T ∈ eligibleTuples g)
    (hd : d ∈ oldWitnessDirections g T D)
    (he : e ∈ freshWitnessDirections g T D) :
    witnessEvent g ((T, (i,j)), (d,e)) = mixedExternalEvent g T d e i j := by
  have hT' := (Finset.mem_filter.mp hT).2
  have hd' := Finset.mem_filter.mp hd
  have he' := (Finset.mem_filter.mp he).2
  ext M
  constructor
  · rintro ⟨hs, hij, _, _, _, _, _, x, hx, hex, hdx, hex'⟩
    exact ⟨⟨⟨lineEval g (tuplePoint M T 0), hs.2.2.2⟩, hs.2.2.1⟩,
      x, hx, hex, hij, hdx, hex'⟩
  · rintro ⟨hs, x, hx, hex, hij, hdx, hex'⟩
    have hde : d ≠ e := by
      intro h
      exact he'.1 (h ▸ hd'.1)
    exact ⟨⟨hT'.1, hT'.2, hs.2, successful_on_tupleTarget hs⟩,
      hij, hde, hd'.2.1, he'.2.1, hd'.2.2, he'.2.2, x, hx, hex, hdx, hex'⟩

theorem mixedOverlap_filter_eq (g : Direction F) (D : Finset (Direction F))
    (M : MergedPairs F) :
    (witnesses g M).filter (mixedOverlapFilter D) =
      (mixedOverlapKeys g D).filter (fun w => M ∈ witnessEvent g w) := by
  ext w
  simp only [Finset.mem_filter, mem_witnesses, mixedOverlapKeys,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, hover, hd, he⟩
    have ht : w.1.1 ∈ eligibleTuples g := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1.1, hw.1.2.1⟩
    refine ⟨⟨⟨ht, hover⟩, ?_, ?_⟩, hw⟩
    · exact Finset.mem_filter.mpr ⟨hd, hw.2.2.2.1, hw.2.2.2.2.2.1⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, he, hw.2.2.2.2.1, hw.2.2.2.2.2.2.1⟩
  · rintro ⟨⟨ht, hd, he⟩, hw⟩
    exact ⟨hw, ht.2,
      (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp he).2.1⟩

theorem integral_mixedOverlapCount_eq_keySum
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (mixedOverlapCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) =
      ∑ w ∈ mixedOverlapKeys g D, conditionalProbability D a (witnessEvent g w) := by
  simp only [mixedOverlapCount, mixedOverlap_filter_eq]
  exact integral_eventCount_eq_sum (exposedLaw D a) (mixedOverlapKeys g D)
    (witnessEvent g)

omit [Field F] in
theorem sum_mixedOverlapKeys (g : Direction F) (D : Finset (Direction F))
    (f : WitnessKey F → ℝ) :
    (∑ w ∈ mixedOverlapKeys g D, f w) =
      ∑ T ∈ (eligibleTuples g).filter
          (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card),
        ∑ d ∈ oldWitnessDirections g T D,
          ∑ e ∈ freshWitnessDirections g T D, ∑ i : Fin 4, ∑ j : Fin 4,
            f ((T,(i,j)),(d,e)) := by
  unfold mixedOverlapKeys
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  conv_rhs => rw [← Finset.sum_ite_mem_eq]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hT : T ∈ (eligibleTuples g).filter
      (fun T => 0 < (PartialAlignment.exposedTupleIndices T D).card)
  · simp only [hT, true_and, ite_true, ite_and, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_mem_eq]
    calc
      _ = ∑ i : Fin 4, ∑ d ∈ oldWitnessDirections g T D,
          ∑ j : Fin 4, ∑ e ∈ freshWitnessDirections g T D,
            f ((T,(i,j)),(d,e)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ d ∈ oldWitnessDirections g T D, ∑ i : Fin 4,
          ∑ j : Fin 4, ∑ e ∈ freshWitnessDirections g T D,
            f ((T,(i,j)),(d,e)) := Finset.sum_comm
      _ = ∑ d ∈ oldWitnessDirections g T D, ∑ i : Fin 4,
          ∑ e ∈ freshWitnessDirections g T D, ∑ j : Fin 4,
            f ((T,(i,j)),(d,e)) := by
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
  · simp only [hT, false_and, ite_false, Finset.sum_const_zero]

theorem integral_mixedOverlapCount_eq
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (mixedOverlapCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) =
      mixedExternalProbabilitySum g D a := by
  rw [integral_mixedOverlapCount_eq_keySum, sum_mixedOverlapKeys]
  unfold mixedExternalProbabilitySum
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [witnessEvent_eq_mixedExternalEvent g D T d e i j
    (Finset.mem_filter.mp hT).1 hd he]

theorem integral_mixedOverlapCount_le
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (mixedOverlapCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      2097152 * ((m : ℝ) + 1)^5 / (Fintype.card F : ℝ) := by
  rw [integral_mixedOverlapCount_eq]
  exact mixedExternalProbabilitySum_le g D a m hD

theorem integral_mixedOverlapCount_le_uniform
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (mixedOverlapCount g D M : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      2097152 * ((m : ℝ) + 1)^5 := by
  apply (integral_mixedOverlapCount_le g D a m hD).trans
  apply div_le_self
  · positivity
  · exact_mod_cast Fintype.card_pos (α := F)

theorem fixed_mixedOverlapCount_le
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F)
    (m : ℕ) (hD : D.card ≤ m) :
    (patternModel g).fixedExpectation D a (fun M => (mixedOverlapCount g D M : ℝ)) ≤
      2097152 * ((m : ℝ) + 1)^5 / (Fintype.card F : ℝ) := by
  rw [patternModel_fixedExpectation_exposed]
  exact integral_mixedOverlapCount_le g D a m hD

end
end Balanced.CandidateMixedExternal

end OAI

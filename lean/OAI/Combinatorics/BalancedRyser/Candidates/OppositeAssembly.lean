import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConstituentMoments
import OAI.Combinatorics.BalancedRyser.Candidates.OppositeFreshMean

namespace OAI

namespace Balanced.OppositeAssembly

noncomputable section
open scoped Classical BigOperators
open CandidateExposure CandidateValidityWitness MeasureTheory ConditionalRestriction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance : MeasurableSpace F := ⊤

def meanBound (m : ℕ) : ℝ :=
  327680 * ((m : ℝ)+1)^4 + 2048 * m + 65536 * m * ((m : ℝ)+1)^4

theorem meanBound_nonneg (m : ℕ) : 0 ≤ meanBound m := by unfold meanBound; positivity

theorem meanBound_mono {m n : ℕ} (h : m ≤ n) : meanBound m ≤ meanBound n := by
  unfold meanBound
  gcongr

theorem witnesses_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((witnesses g M).card : ℝ)) ≤ meanBound m := by
  have hold : (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((oldFreshWitnesses g D M).card : ℝ)) ≤ 2048 * (m : ℝ) := by
    calc
      _ ≤ ∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
          (ExposedOppositeSum.oldOppositeFreshCount g D M : ℝ) := by
        apply Finset.sum_le_sum
        intro M _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        exact_mod_cast oldFreshWitnesses_card_le g D M
      _ ≤ 2048 * (D.card : ℝ) := ExposedOppositeSum.oldOppositeFreshCount_mean_le g D a
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
        (((freshWitnesses g D M).card : ℝ) + ((oldFreshWitnesses g D M).card : ℝ) +
          ((CandidateOldOpposite.overlappingWitnesses g D M).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro M _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast witnesses_card_le_cases g D M
    _ = (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
          ((freshWitnesses g D M).card : ℝ)) +
        (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
          ((oldFreshWitnesses g D M).card : ℝ)) +
        (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
          ((CandidateOldOpposite.overlappingWitnesses g D M).card : ℝ)) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ meanBound m := add_le_add
      (add_le_add (freshWitnesses_mean_le g D a m hD) hold)
      (CandidateOldOpposite.expected_overlappingWitnesses_le g D a m hD)

theorem witness_mem_iff_of_agree (g : Direction F) (w : Label F)
    (M N : MergedPairs F)
    (h : ∀ d ∈ insert w.2 (generatorSet w.1.1), M d = N d) :
    w ∈ witnesses g M ↔ w ∈ witnesses g N := by
  rcases w with ⟨⟨T,i⟩,d⟩
  have hd : M d = N d := h d (Finset.mem_insert_self _ _)
  have hp : tuplePoint M T = tuplePoint N T := by
    funext j
    have hj := h (T.generator j) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
    have hn := h (T.generator (j+1)) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j+1,Finset.mem_univ _,rfl⟩))
    simp only [tuplePoint,constituent,hj,hn]
  simp only [mem_witnesses, successfulInDirection, alignedInDirection,
    Set.mem_ofPred_eq, PairWitness, hp, constituent, hd]

def witnessPatternModel (g : Direction F) : PatternModel where
  Color := Direction F
  Value := fun _ => Bool → F
  law := fun _ => (PMF.uniformOfFintype (Bool → F)).toMeasure
  Label := Label F
  support w := insert w.2 (generatorSet w.1.1)
  event w := {M | w ∈ witnesses g M}
  eventMeasurable _ := (Set.to_countable _).measurableSet
  dependsOn w M N h := witness_mem_iff_of_agree g w M N h

theorem witnessPatternModel_support_card (g : Direction F) (w : Label F) :
    ((witnessPatternModel g).support w).card ≤ 5 := by
  change (insert w.2 (generatorSet w.1.1)).card ≤ 5
  have h := Finset.card_insert_le w.2 (generatorSet w.1.1)
  have hG : (generatorSet w.1.1).card ≤ 4 :=
    Finset.card_image_le.trans (by simp)
  omega

theorem witnessPatternModel_count (g : Direction F) (M : MergedPairs F) :
    (witnessPatternModel g).count M = ((witnesses g M).card : ℝ) := by
  simp only [PatternModel.count,PatternModel.indicator,witnessPatternModel,
    Set.indicator_apply,Set.mem_ofPred_eq]
  rw [← Finset.sum_filter]
  simp
  congr 1
  ext label
  simp only [Finset.mem_filter]
  exact ⟨And.right, fun hlabel => ⟨Finset.mem_univ label, hlabel⟩⟩

theorem witnessPatternModel_fixedExpectation (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (f : MergedPairs F → ℝ) :
    (witnessPatternModel g).fixedExpectation D a f =
      ∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal * f M := by
  have hfix : (witnessPatternModel g).fixCoordinates D a =
      fixArray (fun d => d ∈ D) a := by
    funext M d
    simp only [PatternModel.fixCoordinates,fixArray]
    congr 1
  unfold PatternModel.fixedExpectation
  rw [hfix]
  change (∫ M, f (fixArray (fun d => d ∈ D) a M) ∂Measure.pi
    (fun _ : Direction F => (PMF.uniformOfFintype (Bool → F)).toMeasure)) = _
  rw [integral_fixArray_eq_filtered,PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  congr 1
  funext M
  congr 2
  simp only [CandidateExposure.exposedLaw,PartialAlignment.offsetLaw_eq_uniform]

theorem witnessPatternModel_fixed_count_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (witnessPatternModel g).fixedExpectation D a (witnessPatternModel g).count ≤
      meanBound m := by
  erw [witnessPatternModel_fixedExpectation]
  simp_rw [witnessPatternModel_count]
  exact witnesses_mean_le g D a m hD

theorem witnesses_moment_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((witnesses g M).card : ℝ)^s) ≤ (meanBound (m+(s-1)*5))^s := by
  let P := witnessPatternModel g
  have hbound (K : Finset P.Color) (hK : K.card ≤ (s-1)*5) (y : P.Sample) :
      P.fixedExpectation (D ∪ K) y P.count ≤ meanBound (m+(s-1)*5) := by
    exact witnessPatternModel_fixed_count_le g (D ∪ K) y (m+(s-1)*5)
      ((Finset.card_union_le D K).trans (Nat.add_le_add hD hK))
  have h := P.fixed_moment_le_pow D a 5 s (meanBound (m+(s-1)*5))
    (meanBound_nonneg _) (witnessPatternModel_support_card g) hbound
  erw [witnessPatternModel_fixedExpectation] at h
  simpa only [P,witnessPatternModel_count] using h

end
end Balanced.OppositeAssembly

end OAI

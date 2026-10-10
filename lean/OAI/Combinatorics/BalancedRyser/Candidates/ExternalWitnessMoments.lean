import OAI.Combinatorics.BalancedRyser.Candidates.ExternalFreshGeneratorBound
import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessOldBridge
import OAI.Combinatorics.BalancedRyser.Candidates.FreshExternalCountBound
import OAI.Combinatorics.BalancedRyser.Candidates.MixedExternalAssembly
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentModel

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure PartialAlignment
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance : MeasurableSpace F := ⊤

def exposureConstant (m : ℕ) : ℝ :=
  5242880 * ((m : ℝ) + 1)^4 + 2 *
    (262144 * (m : ℝ)^2 * ((m : ℝ) + 1)^4 +
     2097152 * ((m : ℝ) + 1)^5 +
     (8192 * (m : ℝ)^2 + 32768 * m))

theorem exposureConstant_pos (m : ℕ) : 0 < exposureConstant m := by
  unfold exposureConstant
  positivity

omit [Field F] [Fintype F] in
theorem not_overlap_iff_fresh (T : FourTuple F) (D : Finset (Direction F)) :
    ¬ 0 < (exposedTupleIndices T D).card ↔ ∀ k, T.generator k ∉ D := by
  constructor
  · intro h k hk
    apply h
    exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  · intro h hp
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hp
    exact h k (Finset.mem_filter.mp hk).2

theorem witnesses_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, ((witnesses g M).card : ℝ) ∂(exposedLaw D a).toMeasure) ≤
      exposureConstant m := by
  have hf := FreshExternalWitness.canonical_fresh_count_integral_le g D a m hD
  have ho := oldOld_overlap_integral_le g D a m hD
  have hm := CandidateMixedExternal.integral_mixedOverlapCount_le_uniform g D a m hD
  have hg := freshGenerators_firstOld_integral_le g D a m hD
  have hpart := integral_card_le_four_cases g D
    (fun T => 0 < (exposedTupleIndices T D).card) (exposedLaw D a)
  apply hpart.trans
  apply add_le_add hf
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · apply add_le_add
    · convert ho using 1; first | rfl | (apply integral_congr_ae; filter_upwards [] with M; congr 2; ext w; simp only [Finset.mem_filter])
    · convert hm using 1; first | rfl | (apply integral_congr_ae; filter_upwards [] with M; congr 2; ext w; simp only [Finset.mem_filter, CandidateMixedExternal.mixedOverlapFilter]; tauto)
  · convert hg using 1; first | rfl | (apply integral_congr_ae; filter_upwards [] with M; congr 2; ext w; simp only [Finset.mem_filter, not_overlap_iff_fresh]; tauto)

theorem patternModel_mean_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (patternModel g).fixedExpectation D a (patternModel g).count ≤
      exposureConstant m := by
  rw [patternModel_fixedExpectation_exposed]
  simp_rw [patternModel_count]
  exact witnesses_mean_le g D a m hD

theorem patternModel_moment_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (patternModel g).fixedExpectation D a (fun M => (patternModel g).count M ^ s) ≤
      exposureConstant (m + (s - 1) * 6) ^ s := by
  apply (patternModel g).fixed_moment_le_pow D a 6 s
    (exposureConstant (m + (s - 1) * 6)) (exposureConstant_pos _).le
    (patternModel_support_card_le g)
  intro K hK y
  apply patternModel_mean_le g (D ∪ K) y (m + (s - 1) * 6)
  exact (Finset.card_union_le D K).trans (Nat.add_le_add hD hK)

theorem witnesses_moment_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m s : ℕ) (hD : D.card ≤ m) :
    (∫ M, ((witnesses g M).card : ℝ)^s ∂(exposedLaw D a).toMeasure) ≤
      exposureConstant (m + (s - 1) * 6) ^ s := by
  have h := patternModel_moment_le g D a m s hD
  rw [patternModel_fixedExpectation_exposed] at h
  simpa only [patternModel_count] using h

theorem witnesses_original_moment_le (g : Direction F) (s : ℕ) :
    (∫ M, ((witnesses g M).card : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      exposureConstant ((s - 1) * 6) ^ s := by
  have h := patternModel_moment_le g ∅ (fun _ _ => 0) 0 s (by simp)
  simp only [PatternModel.fixedExpectation] at h
  rw [patternModel_measure] at h
  simp_rw [patternModel_count] at h
  have hfix (M : MergedPairs F) :
      (patternModel g).fixCoordinates ∅ (fun _ _ => 0) M = M := by
    funext d
    simp [PatternModel.fixCoordinates]
  simp_rw [hfix] at h
  simpa only [zero_add] using h

end
end Balanced.ExternalAssembly

end OAI

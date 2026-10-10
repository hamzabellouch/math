import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGlobalLineModel
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceTransport
import OAI.Combinatorics.BalancedRyser.Probability.FiniteMomentTail

namespace OAI

namespace Balanced.CandidateGlobalLine
noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure CandidateIncidence Filter Topology

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance globalLineTailMeasurableSpace : MeasurableSpace F := ⊤

theorem gatedLineModel_conditional_upper_tail (L : Line F)
    (a : MergedPairs F) (s : ℕ) :
    (exposedLaw {L.1} a).toMeasure.real
      {M | 2621441 * (Fintype.card F : ℝ) < (gatedLineModel L).count M} ≤
      globalLineMomentConstant s / (Fintype.card F : ℝ)^s := by
  have hmoment := gatedLineModel_centered_moment_bound L a s
  rw [gatedLineModel_fixedExpectation] at hmoment
  have h := upper_tail_of_centered_moment (exposedLaw {L.1} a).toMeasure
    (gatedLineModel L).count
    ((gatedLineModel L).fixedExpectation {L.1} a (gatedLineModel L).count)
    2621440 (Fintype.card F) (globalLineMomentConstant s) s
    (by exact_mod_cast Fintype.card_pos (α := F))
    (gatedLineModel_initial_mean_le L a) Integrable.of_finite hmoment
  norm_num only [show (2621440+1 : ℝ) = 2621441 by norm_num] at h
  exact h

theorem gatedLineModel_upper_tail (L : Line F) (s : ℕ) :
    (offsetLaw F).toMeasure.real
      {M | 2621441 * (Fintype.card F : ℝ) < (gatedLineModel L).count M} ≤
      globalLineMomentConstant s / (Fintype.card F : ℝ)^s := by
  rw [← gatedLineModel_measure L]
  apply (gatedLineModel L).measureReal_le_of_fixed_indicator_bound
    {L.1} (fun _ _ => 0) _ (Set.toFinite _).measurableSet _
    (div_nonneg (globalLineMomentConstant_nonneg s) (by positivity))
  intro a
  rw [gatedLineModel_fixedExpectation,
    integral_indicator_const _ (Set.toFinite _).measurableSet]
  simpa only [smul_eq_mul, mul_one] using gatedLineModel_conditional_upper_tail L a s

def globalLineCount (L : Line F) (M : MergedPairs F) : ℕ :=
  ∑ g : Direction F, tupleCount (lineHitTest L) g M

theorem globalLineCount_eq_successfulTest (L : Line F) (M : MergedPairs F) :
    globalLineCount L M =
      (CandidateRetentionTransport.successfulTest M
        (fun C => ∃ p ∈ designated M C, OnLine p L)).card := by
  apply Nat.cast_injective (R := ℝ)
  calc
    (globalLineCount L M : ℝ) = (lineModel L).count M := by
      rw [allModel_count]
      simp only [globalLineCount, Nat.cast_sum]
    _ = _ := CandidateRetentionTransport.lineModel_count_eq_successfulTest L M

theorem gatedLineModel_count_eq (L : Line F) (M : MergedPairs F) :
    (gatedLineModel L).count M =
      if L ∉ constituentLines M then (globalLineCount L M : ℝ) else 0 := by
  rw [gatedLineModel_count]
  simp only [globalLineCount, Nat.cast_sum]

theorem globalLineCount_upper_tail (L : Line F) (s : ℕ) :
    (offsetLaw F).toMeasure.real
      {M | L ∉ constituentLines M ∧
        2621441 * (Fintype.card F : ℝ) < globalLineCount L M} ≤
      globalLineMomentConstant s / (Fintype.card F : ℝ)^s := by
  have hset : {M : MergedPairs F | L ∉ constituentLines M ∧
        2621441 * (Fintype.card F : ℝ) < globalLineCount L M} =
      {M | 2621441 * (Fintype.card F : ℝ) < (gatedLineModel L).count M} := by
    ext M
    simp only [Set.mem_ofPred_eq, gatedLineModel_count_eq]
    have hn : (0 : ℝ) ≤ 2621441 * (Fintype.card F : ℝ) := by positivity
    by_cases hM : L ∉ constituentLines M
    · simp [hM]
    · simp [hM, not_lt_of_ge hn]
  rw [hset]
  exact gatedLineModel_upper_tail L s

theorem globalLineCount_any_upper_tail :
    (offsetLaw F).toMeasure.real
      {M | ∃ L : Line F, L ∉ constituentLines M ∧
        2621441 * (Fintype.card F : ℝ) < globalLineCount L M} ≤
      2 * globalLineMomentConstant 4 / (Fintype.card F : ℝ)^2 := by
  let E : Line F → Set (MergedPairs F) := fun L =>
    {M | L ∉ constituentLines M ∧
      2621441 * (Fintype.card F : ℝ) < globalLineCount L M}
  have heq : {M : MergedPairs F | ∃ L : Line F, L ∉ constituentLines M ∧
      2621441 * (Fintype.card F : ℝ) < globalLineCount L M} = ⋃ L, E L := by
    ext M
    simp only [E, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  have hcard : (Fintype.card (Line F) : ℝ) ≤ 2 * (Fintype.card F : ℝ)^2 := by
    simp only [Line, Direction, Fintype.card_prod, Fintype.card_option,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    nlinarith
  calc
    _ ≤ ∑ L : Line F, (offsetLaw F).toMeasure.real (E L) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _L : Line F, globalLineMomentConstant 4 / (Fintype.card F : ℝ)^4 :=
      Finset.sum_le_sum (fun L _ => globalLineCount_upper_tail L 4)
    _ = (Fintype.card (Line F) : ℝ) *
        (globalLineMomentConstant 4 / (Fintype.card F : ℝ)^4) := by simp
    _ ≤ (2 * (Fintype.card F : ℝ)^2) *
        (globalLineMomentConstant 4 / (Fintype.card F : ℝ)^4) :=
      mul_le_mul_of_nonneg_right hcard
        (div_nonneg (globalLineMomentConstant_nonneg 4) (by positivity))
    _ = _ := by field_simp

theorem globalLineCount_all_tendsto_one
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hcard : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => (offsetLaw (F n)).toMeasure.real
      {M | ∀ L : Line (F n), L ∉ constituentLines M →
        (globalLineCount L M : ℝ) ≤ 2621441 * Fintype.card (F n)})
      atTop (𝓝 1) := by
  let bad : ℕ → ℝ := fun n => (offsetLaw (F n)).toMeasure.real
    {M | ∃ L : Line (F n), L ∉ constituentLines M ∧
      2621441 * (Fintype.card (F n) : ℝ) < globalLineCount L M}
  have hqR : Tendsto (fun n => (Fintype.card (F n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcard
  have hbound : Tendsto (fun n => 2 * globalLineMomentConstant 4 /
      (Fintype.card (F n) : ℝ)^2) atTop (𝓝 0) := by
    have h := (hqR.const_div_atTop (2 * globalLineMomentConstant 4)).mul
      (hqR.const_div_atTop 1)
    convert h using 1
    · funext n
      simp only [div_mul_div_comm, mul_one, pow_two]
    · norm_num
  have hbad : Tendsto bad atTop (𝓝 0) :=
    squeeze_zero (fun _ => measureReal_nonneg)
      (fun _ => globalLineCount_any_upper_tail) hbound
  have hall : Tendsto (fun n => 1 - bad n) atTop (𝓝 (1-0 : ℝ)) :=
    tendsto_const_nhds.sub hbad
  have heq (n : ℕ) : (offsetLaw (F n)).toMeasure.real
      {M | ∀ L : Line (F n), L ∉ constituentLines M →
        (globalLineCount L M : ℝ) ≤ 2621441 * Fintype.card (F n)} =
        1 - bad n := by
    have hset : {M : MergedPairs (F n) | ∀ L : Line (F n), L ∉ constituentLines M →
        (globalLineCount L M : ℝ) ≤ 2621441 * Fintype.card (F n)} =
        {M | ∃ L : Line (F n), L ∉ constituentLines M ∧
          2621441 * (Fintype.card (F n) : ℝ) < globalLineCount L M}ᶜ := by
      ext M
      simp
    rw [hset, measureReal_compl (Set.toFinite _).measurableSet]
    simp only [probReal_univ, bad]
  simpa only [sub_zero, ← heq] using hall

theorem globalLineCount_all_probability_tendsto_one
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hcard : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∀ L : Line (F n), L ∉ constituentLines M →
        (globalLineCount L M : ℝ) ≤ 2621441 * Fintype.card (F n)})
      atTop (𝓝 1) := by
  have heq (n : ℕ) (E : Set (MergedPairs (F n))) :
      offsetEventProbability E = (offsetLaw (F n)).toMeasure.real E := by
    rw [offsetEventProbability, Measure.real,
      (offsetLaw (F n)).toMeasure_apply_eq_toOuterMeasure_apply
        ((Set.toFinite E).measurableSet)]
  simpa only [heq] using globalLineCount_all_tendsto_one F hcard

theorem successfulTest_globalLine_all_probability_tendsto_one
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hcard : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∀ L : Line (F n), L ∉ constituentLines M →
        ((CandidateRetentionTransport.successfulTest M
          (fun C => ∃ p ∈ designated M C, OnLine p L)).card : ℝ) ≤
          2621441 * Fintype.card (F n)}) atTop (𝓝 1) := by
  simpa only [globalLineCount_eq_successfulTest] using
    globalLineCount_all_probability_tendsto_one F hcard

end
end Balanced.CandidateGlobalLine

end OAI

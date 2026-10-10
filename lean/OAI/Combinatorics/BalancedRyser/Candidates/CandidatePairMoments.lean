import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePairFibers
import OAI.Combinatorics.BalancedRyser.Probability.FiniteCenteredPatternLemmas

namespace OAI

namespace Balanced.CandidatePairs

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance pairMomentMeasurableSpace : MeasurableSpace F := ⊤

def pairTotalConstant (m : ℕ) : ℝ :=
  (20480 * ((m : ℝ) + 4 + 1)^4) * (20480 * ((m : ℝ) + 1)^4)

def pairFirstOverlapConstant (m : ℕ) : ℝ :=
  (20480 * ((m : ℝ) + 4 + 1)^4) * (16384 * ((m : ℝ) + 1)^4)

def pairExposureConstant (m : ℕ) : ℝ :=
  pairTotalConstant m + 2 * pairFirstOverlapConstant m

theorem pairTotalConstant_nonneg (m : ℕ) : 0 ≤ pairTotalConstant m := by
  unfold pairTotalConstant
  positivity

theorem pairFirstOverlapConstant_nonneg (m : ℕ) : 0 ≤ pairFirstOverlapConstant m := by
  unfold pairFirstOverlapConstant
  positivity

theorem pairExposureConstant_nonneg (m : ℕ) : 0 ≤ pairExposureConstant m :=
  add_nonneg (pairTotalConstant_nonneg m)
    (mul_nonneg (by norm_num) (pairFirstOverlapConstant_nonneg m))

theorem pairPatternModel_total_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (pairPatternModel g).fixedExpectation D a (pairPatternModel g).count ≤
      pairExposureConstant m * Fintype.card F := by
  rw [pairPatternModel_fixedExpectation_exposed]
  simp_rw [pairPatternModel_count_eq_pairCount]
  apply (conditional_pairCount_le D g a m hD).trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact le_add_of_nonneg_right
    (mul_nonneg (by norm_num) (pairFirstOverlapConstant_nonneg m))

theorem pairPatternModel_overlap_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (pairPatternModel g).fixedExpectation D a
      ((pairPatternModel g).overlapCount ∅ D) ≤ pairExposureConstant m := by
  rw [pairPatternModel_fixedExpectation_exposed]
  calc
    _ ≤ ∫ M, 2 * (firstOverlapPairCount D g M : ℝ) ∂(exposedLaw D a).toMeasure := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro M
      exact pairPatternModel_allExposed_overlap_le D g M
    _ = 2 * ∫ M, (firstOverlapPairCount D g M : ℝ) ∂(exposedLaw D a).toMeasure :=
      integral_const_mul _ _
    _ ≤ 2 * pairFirstOverlapConstant m :=
      mul_le_mul_of_nonneg_left (conditional_firstOverlapPairCount_le D g a m hD)
        (by norm_num)
    _ ≤ pairExposureConstant m := le_add_of_nonneg_left (pairTotalConstant_nonneg m)

def pairCenteredMomentConstant (m s : ℕ) : ℝ :=
  ((2*s).factorial : ℝ) * 2^(2*s) *
    (2 * pairExposureConstant (m + 16*s))^(2*s)

theorem pairCenteredMomentConstant_nonneg (m s : ℕ) :
    0 ≤ pairCenteredMomentConstant m s := by
  unfold pairCenteredMomentConstant
  have hC := pairExposureConstant_nonneg (m + 16*s)
  positivity

theorem pairPatternModel_centered_moment_le (g : Direction F)
    (K₀ : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hK : K₀.card ≤ m) :
    (pairPatternModel g).fixedExpectation K₀ a
      (fun M => |(pairPatternModel g).count M -
        (pairPatternModel g).fixedExpectation K₀ a (pairPatternModel g).count|^(2*s)) ≤
      pairCenteredMomentConstant m s * (Fintype.card F : ℝ)^s := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  apply (pairPatternModel g).centered_moment_le_of_allExposedBounds
    K₀ a s 8 (Fintype.card F) (pairExposureConstant (m + 16*s))
    hq (pairExposureConstant_nonneg _) (pairPatternModel_support_card_le g)
  · intro D hD y
    exact pairPatternModel_total_le g D y (m + 16*s) (by omega)
  · intro D hD y
    exact pairPatternModel_overlap_le g D y (m + 16*s) (by omega)

theorem pairCount_centered_moment_le (g : Direction F) (s : ℕ) :
    (∫ M, |(pairCount g M : ℝ) -
      ∫ N, (pairCount g N : ℝ) ∂(offsetLaw F).toMeasure|^(2*s)
      ∂(offsetLaw F).toMeasure) ≤
      pairCenteredMomentConstant 0 s * (Fintype.card F : ℝ)^s := by
  have h := pairPatternModel_centered_moment_le g ∅ (fun _ _ => 0) 0 s (by simp)
  simp only [PatternModel.fixedExpectation] at h
  rw [pairPatternModel_measure] at h
  simp_rw [pairPatternModel_count_eq_pairCount] at h
  exact h

theorem mean_pairCount_le (g : Direction F) :
    (∫ M, (pairCount g M : ℝ) ∂(offsetLaw F).toMeasure) ≤
      pairExposureConstant 0 * Fintype.card F := by
  have h := pairPatternModel_total_le g ∅ (fun _ _ => 0) 0 (by simp)
  simp only [PatternModel.fixedExpectation] at h
  rw [pairPatternModel_measure] at h
  simp_rw [pairPatternModel_count_eq_pairCount] at h
  exact h

def pairLinearThreshold : ℝ := pairExposureConstant 0 + 1

theorem pairLinearThreshold_pos : 0 < pairLinearThreshold := by
  unfold pairLinearThreshold
  linarith [pairExposureConstant_nonneg 0]

theorem pairCount_upper_tail (g : Direction F) :
    (offsetLaw F).toMeasure.real
      {M | pairLinearThreshold * Fintype.card F < (pairCount g M : ℝ)} ≤
      pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ)^2 := by
  let q : ℝ := Fintype.card F
  let μ := (offsetLaw F).toMeasure
  let b : ℝ := ∫ M, (pairCount g M : ℝ) ∂μ
  have hq0 : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := F)
  have hb : b ≤ pairExposureConstant 0 * q := mean_pairCount_le g
  have hsub : {M | pairLinearThreshold * q < (pairCount g M : ℝ)} ⊆
      {M | q^4 ≤ |(pairCount g M : ℝ) - b|^4} := by
    intro M hM
    have hh : (pairExposureConstant 0 + 1) * q < (pairCount g M : ℝ) := hM
    have hd : q ≤ |(pairCount g M : ℝ) - b| :=
      (show q ≤ (pairCount g M : ℝ) - b by nlinarith).trans (le_abs_self _)
    exact pow_le_pow_left₀ hq0.le hd 4
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun M => |(pairCount g M : ℝ) - b|^4)
    (Filter.Eventually.of_forall (fun _ => by positivity)) Integrable.of_finite (q^4)
  have hmoment : (∫ M, |(pairCount g M : ℝ) - b|^4 ∂μ) ≤
      pairCenteredMomentConstant 0 2 * q^2 := by
    simpa only [b, μ, q] using pairCount_centered_moment_le g 2
  have hbound : q^4 * μ.real {M | pairLinearThreshold * q < (pairCount g M : ℝ)} ≤
      pairCenteredMomentConstant 0 2 * q^2 :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity)).trans
      (hm.trans hmoment)
  change μ.real _ ≤ pairCenteredMomentConstant 0 2 / q^2
  calc
    _ ≤ (pairCenteredMomentConstant 0 2 * q^2) / q^4 := by
      apply (le_div_iff₀ (pow_pos hq0 4)).mpr
      simpa only [mul_comm] using hbound
    _ = pairCenteredMomentConstant 0 2 / q^2 := by
      field_simp

theorem pairCount_any_upper_tail :
    (offsetLaw F).toMeasure.real
      {M | ∃ g : Direction F,
        pairLinearThreshold * Fintype.card F < (pairCount g M : ℝ)} ≤
      2 * pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ) := by
  let E : Direction F → Set (MergedPairs F) :=
    fun g => {M | pairLinearThreshold * Fintype.card F < (pairCount g M : ℝ)}
  have heq : {M | ∃ g : Direction F,
      pairLinearThreshold * Fintype.card F < (pairCount g M : ℝ)} = ⋃ g, E g := by
    ext M
    simp [E]
  rw [heq]
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  calc
    _ ≤ ∑ g : Direction F, (offsetLaw F).toMeasure.real (E g) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _g : Direction F, pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ)^2 :=
      Finset.sum_le_sum (fun g _ => pairCount_upper_tail g)
    _ = ((Fintype.card F : ℝ) + 1) *
        (pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ)^2) := by
      simp [Direction, Fintype.card_option]
    _ ≤ (2 * (Fintype.card F : ℝ)) *
        (pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ)^2) := by
      gcongr
      · exact div_nonneg (pairCenteredMomentConstant_nonneg 0 2) (by positivity)
      · linarith
    _ = 2 * pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ) := by
      field_simp

theorem rootFiberSquareCount_any_upper_tail :
    (offsetLaw F).toMeasure.real
      {M | ∃ g : Direction F, pairLinearThreshold * Fintype.card F <
        (TupleAlignment.rootFiberSquareCount M g : ℝ)} ≤
      2 * pairCenteredMomentConstant 0 2 / (Fintype.card F : ℝ) := by
  simpa only [← pairCount_eq_rootFiberSquareCount] using
    (pairCount_any_upper_tail (F := F))

end
end Balanced.CandidatePairs

end OAI

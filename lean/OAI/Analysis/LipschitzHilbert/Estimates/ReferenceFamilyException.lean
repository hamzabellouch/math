import OAI.Analysis.LipschitzHilbert.Fourier.ReferenceLineCount
import OAI.Analysis.LipschitzHilbert.Estimates.CountParameters

namespace OAI

/-!
# The common counting exceptional set

One count is chosen for each reference top, independently of every
separated list. Their finite union has the total-top-area budget of §6.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

def referenceFamilyException {ι : Type*} (T : ι → SlopeBox)
    (N : ι → ℝ × ℝ → ℝ≥0∞) (K lambda : ℝ) : Set (ℝ × ℝ) :=
  ⋃ i, (T i).referenceException (N i) K lambda

theorem measurableSet_referenceFamilyException {ι : Type*} [Countable ι]
    (T : ι → SlopeBox) (N : ι → ℝ × ℝ → ℝ≥0∞)
    (hN : ∀ i, Measurable (N i)) (K lambda : ℝ) :
    MeasurableSet (referenceFamilyException T N K lambda) :=
  MeasurableSet.iUnion fun i => (T i).measurableSet_referenceException (N i) (hN i) K lambda

/-- The actual exceptional union has finite measure, since each of its
reference charts is supported on a bounded rectangle. -/
theorem referenceFamilyException_measure_ne_top {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (N : ι → ℝ × ℝ → ℝ≥0∞) (K lambda : ℝ) :
    (volume.prod volume) (referenceFamilyException T N K lambda) ≠ ∞ := by
  have hsingle (i : ι) :
      (volume.prod volume) ((T i).referenceException (N i) K lambda) ≠ ∞ := by
    unfold SlopeBox.referenceException
    rw [(T i).referenceChart_image_measure]
    apply measure_ne_top_of_subset Set.inter_subset_left
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
  have hsum : (∑ i, (volume.prod volume) ((T i).referenceException (N i) K lambda)) < ∞ :=
    ENNReal.sum_lt_top.mpr (fun i _ => (hsingle i).lt_top)
  exact ((measure_iUnion_fintype_le _ _).trans_lt hsum).ne

/-- Outside the single union, every significant reference has its count
bounded by the same threshold. -/
theorem count_le_outside_referenceFamilyException {ι : Type*}
    (T : ι → SlopeBox) (N : ι → ℝ × ℝ → ℝ≥0∞) {K lambda : ℝ}
    {z : ℝ × ℝ} (hout : z ∉ referenceFamilyException T N K lambda)
    (i : ι) (hsignificant : (T i).radius z ≤ K) :
    N i (((T i).referenceChart.symm z).2, z.1) ≤ ENNReal.ofReal lambda := by
  apply (T i).count_le_outside_referenceException (N i) hsignificant
  intro hi
  exact hout (Set.mem_iUnion.mpr ⟨i, hi⟩)

theorem referenceFamilyException_measure_bound {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (N : ι → ℝ × ℝ → ℝ≥0∞) {K P θ c lambda : ℝ}
    (hbound : ∀ i,
      (volume.prod volume).real ((T i).referenceException (N i) K lambda) ≤
        384 * K * (K + P) * (T i).length * (T i).width *
          Real.exp (-θ * lambda / (240 * (1 + c)))) :
    (volume.prod volume).real (referenceFamilyException T N K lambda) ≤
      (∑ i, (T i).length * (T i).width) *
        (384 * K * (K + P) * Real.exp (-θ * lambda / (240 * (1 + c)))) := by
  calc
    _ ≤ ∑ i, (volume.prod volume).real ((T i).referenceException (N i) K lambda) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, ((T i).length * (T i).width) *
        (384 * K * (K + P) * Real.exp (-θ * lambda / (240 * (1 + c)))) := by
      apply Finset.sum_le_sum
      intro i _
      convert hbound i using 1
      ring
    _ = _ := (Finset.sum_mul ..).symm

/-- Actual reference counts exist simultaneously for the finite top
family. The counts are fixed before the threshold and before the list. -/
theorem reference_family_count_setup {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (u : ℝ × ℝ → ℝ) (hu : Measurable u)
    {M : ℕ} (hM : 0 < M) {c K P θ : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M)
    (hK : 0 ≤ K) (hP : 0 < P) (hθ : 0 < θ) :
    ∃ N : ι → ℝ × ℝ → ℝ≥0∞, (∀ i, Measurable (N i)) ∧
      (∀ i, (T i).ReferencePopularCount u c P θ M (N i)) ∧
      ∀ lambda : ℝ, 0 ≤ lambda →
        MeasurableSet (referenceFamilyException T N K lambda) ∧
        (volume.prod volume).real (referenceFamilyException T N K lambda) ≤
          (∑ i, (T i).length * (T i).width) *
            (384 * K * (K + P) * Real.exp (-θ * lambda / (240 * (1 + c)))) := by
  classical
  choose N hN hpopular htail using
    (fun i => (T i).reference_count_setup u hu hM hc hcM hK hP hθ)
  refine ⟨N, hN, hpopular, ?_⟩
  intro lambda hlambda
  exact ⟨measurableSet_referenceFamilyException T N hN K lambda,
    referenceFamilyException_measure_bound T N (fun i => htail i lambda hlambda)⟩

/-- A polynomial prefactor in the family-area estimate is absorbed by
the Gaussian tail, giving exactly the requested `S exp(-J L)` budget. -/
theorem referenceFamilyException_exponential_budget {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (E : Set (ℝ × ℝ)) {C c J a L : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hL : 1 ≤ L)
    (hlarge : (|Real.log C| + |a| + J) / c ≤ L)
    (hmeasure : (volume.prod volume).real E ≤
      (∑ i, (T i).length * (T i).width) * (C * L ^ a * Real.exp (-c * L ^ 2))) :
    (volume.prod volume).real E ≤
      (∑ i, (T i).length * (T i).width) * Real.exp (-J * L) := by
  apply hmeasure.trans
  apply mul_le_mul_of_nonneg_left (polynomial_gaussian_le_exponential hC hc hL hlarge)
  exact Finset.sum_nonneg fun i _ => mul_nonneg (T i).length_pos.le (T i).width_pos.le

end LipschitzHilbert

end

end OAI

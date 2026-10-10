import OAI.NumberTheory.Jacobsthal.Estimates.AdmittedHighRemoval
import OAI.NumberTheory.Jacobsthal.Probability.SubMarkovFlagPowers

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousHighPartition

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures RegeneratingInverseBands ArrivalKernelGeometry
open AdmittedHarmonicPaths LowStateHorizon SubMarkovFlagPowers
open PersistentFailureFlag FlaggedOccupationBound

def high (S : ℝ) (z : CostState) : Prop := S < stateRatio z.1

theorem high_measurable (S : ℝ) : MeasurableSet {z | high S z} :=
  measurableSet_lt measurable_const (stateRatio_measurable.comp measurable_fst)

theorem good_admitted_eq_low (K : Kernel CostState CostState) (v ell S : ℝ) :
    goodKernel (K.restrict (arrivalSet_measurable v ell)) (high_measurable S) = lowKernel K v ell S := by
  ext z : 1
  simp only [goodKernel,lowKernel,Kernel.restrict_apply,Measure.restrict_restrict (high_measurable S).compl]
  congr 1
  ext y
  simp only [lowDomain,mem_inter_iff,mem_compl_iff,mem_ofPred_eq,high,not_lt]
  exact and_comm

theorem marked_harmonic_eq (v ell S : ℝ) :
    marked (admittedHarmonic v ell) (high_measurable S) = FlaggedHarmonicPaths.kernel v ell S := by
  ext z : 1
  rw [marked_eq_map_sfinite,FlaggedHarmonicPaths.kernel_eq_map]
  congr 1
  funext y
  by_cases hy : S < stateRatio y.1 <;>
    cases z.2 <;> simp [FlaggedHarmonicPaths.flagUpdate,badBit,high,hy]

noncomputable def tiltedFlagged (v ell S : ℝ) : Kernel (CostState×Bool) (CostState×Bool) :=
  marked (admittedTilted v ell) (high_measurable S)

theorem harmonic_finite_partition (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (n : ℕ) (z : CostState) (hz : stateRatio z.1 ≤ S) :
    (∫⁻ y,F y ∂((admittedHarmonic v ell)^n) z) =
      (∫⁻ y,F y ∂((lowKernel HarmonicWeightKernel.harmonicKernel v ell S)^n) z)+
      (∫⁻ y,selected F y ∂((FlaggedHarmonicPaths.kernel v ell S)^n) (FlaggedHarmonicPaths.initial S z)) := by
  have h := finite_integral_partition (admittedHarmonic v ell) (high_measurable S) hF n z
  have he : goodKernel (admittedHarmonic v ell) (high_measurable S) =
      lowKernel HarmonicWeightKernel.harmonicKernel v ell S :=
    good_admitted_eq_low HarmonicWeightKernel.harmonicKernel v ell S
  rw [he,marked_harmonic_eq] at h
  simpa only [FlaggedHarmonicPaths.initial,ite_eq_right (not_lt.mpr hz)] using h

theorem tilted_finite_partition (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (n : ℕ) (z : CostState) :
    (∫⁻ y,F y ∂((admittedTilted v ell)^n) z) =
      (∫⁻ y,F y ∂((lowKernel costKernel v ell S)^n) z)+
      (∫⁻ y,selected F y ∂((tiltedFlagged v ell S)^n) (z,false)) := by
  have h := finite_integral_partition (admittedTilted v ell) (high_measurable S) hF n z
  have he : goodKernel (admittedTilted v ell) (high_measurable S) = lowKernel costKernel v ell S :=
    good_admitted_eq_low costKernel v ell S
  rw [he] at h
  exact h

theorem harmonic_high_compact_bound (v ell S : ℝ) (z : CostState) {F : CostState → ℝ≥0∞}
    {D : ℝ≥0∞} (hD : D ≠ ∞) {K : ℝ} (hbound : ∀ y,F y ≤ D)
    (hsupport : ∀ y,K < gapValue v y → F y=0) :
    (∑' n : ℕ,∫⁻ y,selected F y ∂((FlaggedHarmonicPaths.kernel v ell S)^n) (FlaggedHarmonicPaths.initial S z)) ≤
      D*AdmittedHighRemoval.lowHighMass v ell S z K := by
  have hA : MeasurableSet {y : CostState×Bool | y.2=true ∧ gapValue v y.1 ≤ K} :=
    (measurable_snd (measurableSet_singleton true)).inter
      (measurableSet_le ((gapValue_measurable v).comp measurable_fst) measurable_const)
  have hpoint : ∀ y : CostState×Bool,selected F y ≤
      D*{y : CostState×Bool | y.2=true ∧ gapValue v y.1 ≤ K}.indicator (fun _ => (1:ℝ≥0∞)) y := by
    rintro ⟨y,b⟩
    cases b with
    | false => simp [selected,failed]
    | true =>
      by_cases hy : gapValue v y ≤ K
      · simp [selected,failed,hy,hbound y]
      · simp [selected,failed,hy,hsupport y (lt_of_not_ge hy)]
  unfold AdmittedHighRemoval.lowHighMass
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ ∫⁻ y,D*{y : CostState×Bool | y.2=true ∧ gapValue v y.1 ≤ K}.indicator (fun _ => (1:ℝ≥0∞)) y
        ∂((FlaggedHarmonicPaths.kernel v ell S)^n) (FlaggedHarmonicPaths.initial S z) := lintegral_mono hpoint
    _ = _ := by rw [lintegral_const_mul' _ _ hD,lintegral_indicator hA,setLIntegral_const,one_mul]

end NumberTheoryLean.ContinuousHighPartition

end

end Erdos970

end OAI

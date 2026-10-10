import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def cappedExcess (ν : Measure X) (μ : ProbabilityMeasure X) : ℝ≥0∞ :=
  ⨆ f : X →ᵇ ℝ, ⨆ (_ : ∀ x, 0 ≤ f x ∧ f x ≤ 1),
    ENNReal.ofReal ((∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂ν)

lemma cappedExcess_lowerSemicontinuous (ν : Measure X) :
    LowerSemicontinuous (cappedExcess ν) := by
  apply lowerSemicontinuous_iSup
  intro f
  apply lowerSemicontinuous_iSup
  intro _
  exact (ENNReal.continuous_ofReal.comp
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).sub
      continuous_const)).lowerSemicontinuous

omit [BorelSpace X] in
lemma cappedExcess_query_le (ν : Measure X) (μ : ProbabilityMeasure X)
    (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ENNReal.ofReal ((∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂ν) ≤ cappedExcess ν μ :=
  le_iSup_of_le f (le_iSup_of_le hf le_rfl)

lemma cappedExcess_le_one (ν : Measure X) (μ : ProbabilityMeasure X) :
    cappedExcess ν μ ≤ 1 := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  have hμ : (∫ x, f x ∂(μ : Measure X)) ≤ 1 := by
    calc
      _ ≤ ∫ _ : X, (1:ℝ) ∂(μ : Measure X) :=
        integral_mono (f.integrable _) (integrable_const _) (fun x => (hf x).2)
      _ = 1 := by simp
  have hν : 0 ≤ ∫ x, f x ∂ν := integral_nonneg (fun x => (hf x).1)
  exact (ENNReal.ofReal_le_ofReal (by linarith :
    (∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂ν ≤ 1)).trans_eq (by simp)

lemma cappedExcess_closed_query_le (ν : Measure X) [IsFiniteMeasure ν]
    (μ : ProbabilityMeasure X) {A : Set X} (hA : IsClosed A) :
    ENNReal.ofReal (((μ : Measure X) A).toReal - (ν A).toReal) ≤ cappedExcess ν μ := by
  let f : ℕ → X →ᵇ ℝ := fun n =>
    BoundedContinuousFunction.comp NNReal.toReal NNReal.isometry_coe.lipschitzWith (hA.apprSeq n)
  have hf (n : ℕ) (x : X) : 0 ≤ f n x ∧ f n x ≤ 1 := by
    change 0 ≤ ((hA.apprSeq n x : ℝ≥0) : ℝ) ∧ ((hA.apprSeq n x : ℝ≥0) : ℝ) ≤ 1
    exact ⟨NNReal.coe_nonneg _, by exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hA n x⟩
  have ht (η : Measure X) [IsFiniteMeasure η] :
      Tendsto (fun n => ∫ x, f n x ∂η) atTop (𝓝 ((η A).toReal)) := by
    have H := (ENNReal.tendsto_toReal (measure_ne_top η A)).comp
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hA η)
    change Tendsto (fun n => (∫⁻ x, (hA.apprSeq n x : ℝ≥0∞) ∂η).toReal) _ _ at H
    simpa only [BoundedContinuousFunction.toReal_lintegral_coe_eq_integral, f, BoundedContinuousFunction.comp_apply] using H
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((ht (μ:Measure X)).sub (ht ν)))
  exact Eventually.of_forall (fun n => cappedExcess_query_le ν μ (f n) (hf n))

lemma cappedExcess_eq_zero_iff (ν : Measure X) [IsFiniteMeasure ν] (μ : ProbabilityMeasure X) :
    cappedExcess ν μ = 0 ↔ (μ : Measure X) ≤ ν := by
  constructor
  · intro he
    have hcl {A : Set X} (hA : IsClosed A) : (μ : Measure X) A ≤ ν A := by
      have h := cappedExcess_closed_query_le ν μ hA
      rw [he,nonpos_iff_eq_zero,ENNReal.ofReal_eq_zero] at h
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (sub_nonpos.mp h)
    apply Measure.le_iff.mpr
    intro A hA
    rw [hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top (μ:Measure X) A)]
    apply iSup_le
    intro B
    apply iSup_le
    intro hB
    apply iSup_le
    intro hBc
    exact (hcl hBc).trans (measure_mono hB)
  · intro h
    apply le_antisymm _ bot_le
    apply iSup_le
    intro f
    apply iSup_le
    intro hf
    exact ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr
      (integral_mono_measure h (Eventually.of_forall fun x => (hf x).1) (f.integrable ν))) |>.le

lemma exists_cappedExcess_minimizer (ν : Measure X) {S : Set (ProbabilityMeasure X)}
    (hne : S.Nonempty) (hc : IsCompact S) :
    ∃ μ ∈ S, ∀ ρ ∈ S, cappedExcess ν μ ≤ cappedExcess ν ρ := by
  simpa only [isMinOn_iff] using
    (cappedExcess_lowerSemicontinuous ν).lowerSemicontinuousOn S |>.exists_isMinOn hne hc

lemma measure_le_add_cappedExcess (ν : Measure X) [IsFiniteMeasure ν]
    (μ : ProbabilityMeasure X) {A : Set X} (hA : MeasurableSet A) :
    (μ : Measure X) A ≤ ν A + cappedExcess ν μ := by
  have hcl {B : Set X} (hB : IsClosed B) :
      (μ : Measure X) B ≤ ν B + cappedExcess ν μ := by
    have H := cappedExcess_closed_query_le ν μ hB
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at H
    exact (tsub_le_iff_right.mp H).trans_eq (add_comm _ _)
  rw [hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top (μ:Measure X) A)]
  exact iSup_le fun B => iSup_le fun hB => iSup_le fun hBc =>
    (hcl hBc).trans (add_le_add (measure_mono hB) le_rfl)

omit [MetricSpace X] [BorelSpace X] in
lemma measure_le_sub_add (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ ≤ (μ - ν) + ν := by
  obtain ⟨S,hS⟩ := exists_isHahnDecomposition μ ν
  have hh : μ.restrict Sᶜ = (μ-ν).restrict Sᶜ + ν.restrict Sᶜ := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hS.measurableSet.compl]
    exact (Measure.sub_add_cancel_of_le hS.ge_on_compl).symm
  calc
    μ = μ.restrict S + μ.restrict Sᶜ := (Measure.restrict_add_restrict_compl hS.measurableSet).symm
    _ ≤ ν.restrict S + ((μ-ν).restrict Sᶜ + ν.restrict Sᶜ) := by
      rw [hh]
      exact add_le_add hS.le_on le_rfl
    _ = (μ-ν).restrict Sᶜ + (ν.restrict S + ν.restrict Sᶜ) := by abel
    _ = (μ-ν).restrict Sᶜ + ν := by rw [Measure.restrict_add_restrict_compl hS.measurableSet]
    _ ≤ (μ-ν)+ν := add_le_add Measure.restrict_le_self le_rfl

omit [MetricSpace X] [BorelSpace X] in
lemma positivePart_total_of_hahn (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set X} (hS : IsHahnDecomposition μ ν S) :
    (μ-ν) univ = μ Sᶜ - ν Sᶜ := by
  calc
    (μ-ν) univ = (μ-ν) Sᶜ := by
      rw [← measure_add_measure_compl hS.measurableSet,
        Measure.sub_apply_eq_zero_of_isHahnDecomposition hS,zero_add]
    _ = ((μ-ν).restrict Sᶜ) univ := by simp
    _ = (μ.restrict Sᶜ - ν.restrict Sᶜ) univ := by
      rw [Measure.restrict_sub_eq_restrict_sub_restrict hS.measurableSet.compl]
    _ = μ Sᶜ - ν Sᶜ := by
      rw [Measure.sub_apply MeasurableSet.univ hS.ge_on_compl]
      simp

lemma cappedExcess_eq_positivePart (ν : Measure X) [IsFiniteMeasure ν]
    (μ : ProbabilityMeasure X) : cappedExcess ν μ = ((μ:Measure X)-ν) univ := by
  let δ := (μ:Measure X)-ν
  let : IsFiniteMeasure δ := isFiniteMeasure_of_le (μ:Measure X) Measure.sub_le
  apply le_antisymm
  · apply iSup_le
    intro f
    apply iSup_le
    intro hf
    have H := integral_mono_measure (measure_le_sub_add (μ:Measure X) ν)
      (Eventually.of_forall fun x => (hf x).1) (f.integrable (δ+ν))
    rw [integral_add_measure (f.integrable δ) (f.integrable ν)] at H
    have Hb : (∫ x, f x ∂δ) ≤ (δ univ).toReal := by
      calc
        _ ≤ ∫ _ : X, (1:ℝ) ∂δ := integral_mono (f.integrable δ)
          (integrable_const _) (fun x => (hf x).2)
        _ = _ := by simp [Measure.real]
    calc
      _ ≤ ENNReal.ofReal ((δ univ).toReal) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top δ univ)
  · obtain ⟨S,hS⟩ := exists_isHahnDecomposition (μ:Measure X) ν
    rw [positivePart_total_of_hahn _ _ hS]
    exact tsub_le_iff_right.mpr (by
      simpa only [add_comm] using measure_le_add_cappedExcess ν μ hS.measurableSet.compl)

end WeakHessian

end
end InlinedFile0

end OAI

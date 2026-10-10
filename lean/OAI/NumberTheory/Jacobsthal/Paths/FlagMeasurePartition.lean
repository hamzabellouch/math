import OAI.NumberTheory.Jacobsthal.Analysis.CompactTestMeasurable
import OAI.NumberTheory.Jacobsthal.Probability.SubMarkovFlagPowers

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FlagMeasurePartition

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag FlaggedOccupationBound SubMarkovFlagPowers

variable {α : Type*} [MeasurableSpace α]

noncomputable def highPart (K : Kernel α α) {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (x : α) : Measure α :=
  ((((marked K hBad)^n) (x,false)).restrict failed).map Prod.fst

theorem power_measure_partition (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (x : α) :
    (K^n) x = ((goodKernel K hBad)^n) x+highPart K hBad n x := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_add_measure,highPart,lintegral_map hF measurable_fst,
    ← lintegral_indicator failed_measurable]
  exact finite_integral_partition K hBad hF n x

theorem signed_power_difference (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (x : α) {F : α → ℝ}
    (hF : Measurable F) (hI : Integrable F ((K^n) x)) :
    ENNReal.ofReal |(∫ y,F y ∂(K^n) x)-(∫ y,F y ∂((goodKernel K hBad)^n) x)| ≤
      ∫⁻ y,selected (fun a => ENNReal.ofReal |F a|) y ∂((marked K hBad)^n) (x,false) := by
  have he := power_measure_partition K hBad n x
  have hl : ((goodKernel K hBad)^n) x ≤ (K^n) x := by rw [he]; exact Measure.le_add_right le_rfl
  have hh : highPart K hBad n x ≤ (K^n) x := by rw [he]; exact Measure.le_add_left le_rfl
  have hIl := hI.mono_measure hl
  have hIh := hI.mono_measure hh
  have hid : (∫ y,F y ∂(K^n) x)-(∫ y,F y ∂((goodKernel K hBad)^n) x) = ∫ y,F y ∂highPart K hBad n x := by
    rw [he,integral_add_measure hIl hIh]
    ring
  rw [hid]
  have h := enorm_integral_le_lintegral_enorm (μ:=highPart K hBad n x) F
  simp only [Real.enorm_eq_ofReal_abs] at h
  rw [highPart,lintegral_map (f:=fun a => ENNReal.ofReal |F a|) (ENNReal.measurable_ofReal.comp hF.abs) measurable_fst,
    ← lintegral_indicator failed_measurable] at h
  exact h

theorem signed_finite_difference (K : Kernel α α) [IsSFiniteKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (N : ℕ) (x : α) {F : α → ℝ}
    (hF : Measurable F) (hI : ∀ n ∈ range N,Integrable F ((K^n) x)) :
    ENNReal.ofReal |(∑ n ∈ range N,∫ y,F y ∂(K^n) x)-
      (∑ n ∈ range N,∫ y,F y ∂((goodKernel K hBad)^n) x)| ≤
      ∑ n ∈ range N,∫⁻ y,selected (fun a => ENNReal.ofReal |F a|) y ∂((marked K hBad)^n) (x,false) := by
  rw [← Finset.sum_sub_distrib]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  exact Finset.sum_le_sum (fun n hn => signed_power_difference K hBad n x hF (hI n hn))

end NumberTheoryLean.FlagMeasurePartition

end

end Erdos970

end OAI

import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FiniteMonotoneComparison

open Filter Set Finset MeasureTheory
open scoped ENNReal

 theorem finite_level_bound (μ ν : Measure ℝ) (A : Finset ℝ) (f : ℝ → ℝ) (a M t : ℝ) (E : ℝ≥0∞)
    (hsupport : ∀ᵐ x ∂μ, x ∈ A) (hloc : ∀ x ∈ A, a ≤ x)
    (hanti : AntitoneOn f (Ici a)) (hM : ∀ x ∈ A, f x ≤ M)
    (hcdf : ∀ x ∈ A, μ (Icc a x) ≤ ν (Icc a x) + E) :
    μ {x | t < f x} ≤ ν {x | t < f x} + (Iio M).indicator (fun _ => E) t := by
  classical
  let B := A.filter (fun x => t < f x)
  by_cases hB : B.Nonempty
  · let x := B.max' hB
    have hxB : x ∈ B := B.max'_mem hB
    have hx : x ∈ A := (Finset.mem_filter.mp hxB).1
    have htx : t < f x := (Finset.mem_filter.mp hxB).2
    have htM : t < M := htx.trans_le (hM x hx)
    rw [indicator_of_mem (show t ∈ Iio M from htM)]
    have hμ : μ {y | t < f y} ≤ μ (Icc a x) := by
      apply measure_mono_ae
      filter_upwards [hsupport] with y hy
      intro hyt
      exact ⟨hloc y hy, B.le_max' y (Finset.mem_filter.mpr ⟨hy,hyt⟩)⟩
    have hν : ν (Icc a x) ≤ ν {y | t < f y} := by
      apply measure_mono
      intro y hy
      exact htx.trans_le (hanti hy.1 (hloc x hx) hy.2)
    exact hμ.trans ((hcdf x hx).trans (add_le_add hν le_rfl))
  · have hz : μ {x | t < f x} = 0 := by
      have hAE : ∀ᵐ x ∂μ, ¬ t < f x := by
        filter_upwards [hsupport] with x hx
        intro hxt
        exact hB ⟨x, Finset.mem_filter.mpr ⟨hx,hxt⟩⟩
      simpa only [ae_iff, not_not] using hAE
    rw [hz]
    exact zero_le

theorem level_measure_measurable (ν : Measure ℝ) (f : ℝ → ℝ) :
    Measurable (fun t : ℝ => ν {x | t < f x}) := by
  have h : Antitone (fun t : ℝ => ν {x | t < f x}) := by
    intro s t hst
    apply measure_mono
    intro x hx
    exact hst.trans_lt hx
  exact h.measurable

theorem finite_monotone_integral_le (μ ν : Measure ℝ) (A : Finset ℝ) (f : ℝ → ℝ) (a M : ℝ) (E : ℝ≥0∞)
    (hf : Measurable f) (hsupport : ∀ᵐ x ∂μ, x ∈ A) (hloc : ∀ x ∈ A, a ≤ x)
    (hnonneg : ∀ x ∈ A, 0 ≤ f x) (hνnonneg : 0 ≤ᵐ[ν] f)
    (hanti : AntitoneOn f (Ici a)) (hM : ∀ x ∈ A, f x ≤ M)
    (hcdf : ∀ x ∈ A, μ (Icc a x) ≤ ν (Icc a x) + E) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂ν) + E * ENNReal.ofReal M := by
  have hμnonneg : 0 ≤ᵐ[μ] f := hsupport.mono (fun x hx => hnonneg x hx)
  rw [lintegral_eq_lintegral_meas_lt μ hμnonneg hf.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν hνnonneg hf.aemeasurable]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ν {x | t < f x} + (Iio M).indicator (fun _ => E) t :=
      lintegral_mono (fun t => finite_level_bound μ ν A f a M t E hsupport hloc hanti hM hcdf)
    _ = (∫⁻ t in Ioi (0 : ℝ), ν {x | t < f x}) +
        ∫⁻ t in Ioi (0 : ℝ), (Iio M).indicator (fun _ => E) t :=
      lintegral_add_left (level_measure_measurable ν f) _
    _ = _ := by
      rw [lintegral_indicator measurableSet_Iio, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iio]
      have hi : Iio M ∩ Ioi (0 : ℝ) = Ioo 0 M := by ext t; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]; tauto
      rw [hi, Real.volume_Ioo, sub_zero]

end NumberTheoryLean.FiniteMonotoneComparison

end

end Erdos970

end OAI

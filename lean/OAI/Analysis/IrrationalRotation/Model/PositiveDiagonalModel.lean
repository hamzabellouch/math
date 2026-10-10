import OAI.Analysis.IrrationalRotation.Model.FieldDiagonal
import Mathlib.Topology.Algebra.Module.Equiv

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.PositiveDiagonalModel

abbrev Fiber := WeightedShift.Hilbert
abbrev Space {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) := Lp Fiber 2 μ

def e0 : Fiber := lp.single 2 (0 : ℤ) (1 : ℂ)

def fiberShift : Fiber →L[ℂ] Fiber :=
  (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap

def fiberShiftUnit : (Fiber →L[ℂ] Fiber)ˣ :=
  (ContinuousLinearEquiv.unitsEquiv ℂ Fiber).symm
    (WeightedShift.shift 1).toContinuousLinearEquiv

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

def integerIterate (σ : Y ≃ᵐ Y) : ℤ → Y → Y
  | .ofNat n => (σ : Y → Y)^[n]
  | .negSucc n => (σ.symm : Y → Y)^[n + 1]

theorem measurable_integerIterate (σ : Y ≃ᵐ Y) (k : ℤ) :
    Measurable (integerIterate σ k) := by
  cases k with
  | ofNat n => exact σ.measurable.iterate n
  | negSucc n => exact σ.symm.measurable.iterate (n + 1)

def orbitArray (σ : Y ≃ᵐ Y) (f : Y → ℝ) (y : Y) (k : ℤ) : ℝ :=
  f (integerIterate σ k y)

def realWeight (a : Y → ℤ → ℝ) (C : ℝ)
    (hbound : ∀ y k, |a y k| ≤ C) (y : Y) : WeightedShift.Weight :=
  ⟨fun k => (a y k : ℂ), memℓp_infty <| by
    refine ⟨C, ?_⟩
    rintro r ⟨k, rfl⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hbound y k⟩

def realDiagonal (a : Y → ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y k, |a y k| ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun y => a y k) μ) :
    Space μ →L[ℂ] Space μ :=
  WeightedShift.fieldDiagonal (realWeight a C hbound) C hC
    (fun y => lp.norm_le_of_forall_le hC (fun k => by
      simpa only [realWeight, Complex.norm_real, Real.norm_eq_abs] using hbound y k))
    (fun k => Complex.continuous_ofReal.comp_aestronglyMeasurable (hm k))

def realWeightedShift (a : Y → ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y k, |a y k| ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun y => a y k) μ) :
    Space μ →L[ℂ] Space μ :=
  (fiberShift.compLpL 2 μ) * realDiagonal a C hC hbound hm

def orbitWeightedShift (σ : Y ≃ᵐ Y) (f : Y → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, |f y| ≤ C) (hf : Measurable f) : Space μ →L[ℂ] Space μ :=
  realWeightedShift (orbitArray σ f) C hC
    (fun y k => hbound (integerIterate σ k y))
    (fun k => (hf.comp (measurable_integerIterate σ k)).aestronglyMeasurable)

theorem exists_bounded_measurable_representative (f : Lp ℝ ∞ μ) :
    ∃ g : Y → ℝ, Measurable g ∧ g =ᵐ[μ] f ∧ ∀ y, |g y| ≤ ‖f‖ := by
  let g₀ := (Lp.aestronglyMeasurable f).mk f
  have hm : Measurable g₀ := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.measurable
  have heq : g₀ =ᵐ[μ] f := (Lp.aestronglyMeasurable f).ae_eq_mk.symm
  have hb : ∀ᵐ y ∂μ, |f y| ≤ ‖f‖ := by
    filter_upwards [ae_le_eLpNormEssSup (f := (f : Y → ℝ)) (μ := μ)] with y hy
    have hfin : eLpNormEssSup f μ ≠ ∞ := by
      simpa only [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] using Lp.eLpNorm_ne_top f
    have hle := ENNReal.toReal_mono hfin hy
    simpa only [toReal_enorm, Real.norm_eq_abs, Lp.norm_def,
      eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] using hle
  let g : Y → ℝ := fun y => if |g₀ y| ≤ ‖f‖ then g₀ y else 0
  refine ⟨g, hm.ite (measurableSet_le (continuous_abs.measurable.comp hm) measurable_const) measurable_const, ?_, ?_⟩
  · filter_upwards [heq, hb] with y hy hby
    simp only [g, hy, ite_eq_left hby]
  · intro y
    by_cases hy : |g₀ y| ≤ ‖f‖
    · simpa only [g, ite_eq_left hy] using hy
    · simpa only [g, ite_eq_right hy, abs_zero] using norm_nonneg f

def boundedRepresentative (f : Lp ℝ ∞ μ) : Y → ℝ :=
  Classical.choose (exists_bounded_measurable_representative f)

theorem boundedRepresentative_measurable (f : Lp ℝ ∞ μ) :
    Measurable (boundedRepresentative f) :=
  (Classical.choose_spec (exists_bounded_measurable_representative f)).1

theorem boundedRepresentative_ae_eq (f : Lp ℝ ∞ μ) :
    boundedRepresentative f =ᵐ[μ] f :=
  (Classical.choose_spec (exists_bounded_measurable_representative f)).2.1

theorem boundedRepresentative_bound (f : Lp ℝ ∞ μ) (y : Y) :
    |boundedRepresentative f y| ≤ ‖f‖ :=
  (Classical.choose_spec (exists_bounded_measurable_representative f)).2.2 y

def lpOrbitWeightedShift (σ : Y ≃ᵐ Y) (f : Lp ℝ ∞ μ) :
    Space μ →L[ℂ] Space μ :=
  orbitWeightedShift σ (boundedRepresentative f) ‖f‖ (norm_nonneg f)
    (boundedRepresentative_bound f) (boundedRepresentative_measurable f)

def diagonalState [IsFiniteMeasure μ] (P : Space μ →L[ℂ] Space μ) : ℝ :=
  (inner ℂ (Lp.const 2 μ e0) (P (Lp.const 2 μ e0))).re

end Invariant233.PositiveDiagonalModel

end

end OAI

import OAI.Analysis.CircleDomains.Sobolev.SphericalAreaLocalization
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! Finite spherical quadratic energy supplies finite planar line density
on almost every horizontal and vertical line in each compact chart patch. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem ennreal_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  by_cases h : a ≤ 1
  · exact h.trans le_self_add
  · have ha : 1 ≤ a := le_of_not_ge h
    calc
      a = a * 1 := (mul_one a).symm
      _ ≤ a * a := mul_le_mul' le_rfl ha
      _ ≤ 1 + a ^ 2 := by rw [pow_two]; exact le_add_self

theorem lintegral_lt_top_of_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (g : X → ℝ≥0∞)
    (hg : (∫⁻x, g x ^ 2 ∂μ) < ∞) : (∫⁻x, g x ∂μ) < ∞ := by
  apply lt_of_le_of_lt (lintegral_mono fun x => ennreal_le_one_add_sq (g x))
  rw [lintegral_add_left measurable_const, lintegral_const, one_mul]
  exact ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ, hg⟩

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem planar_density_on_compact_finite
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    {K : Set ℂ} (hK : IsCompact K) : (∫⁻z in K, g (z : Sphere)) < ∞ := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply lintegral_lt_top_of_sq
  apply planar_energy_on_compact_finite hK
  rwa [← lintegral_sphericalArea _ (hg.pow_const 2)]

theorem ae_finite_planar_density_slices
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    {K : Set ℂ} (hK : IsCompact K) :
    (∀ᵐ y : ℝ, (∫⁻x : ℝ, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩) < ∞) ∧
    (∀ᵐ x : ℝ, (∫⁻y : ℝ, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩) < ∞) := by
  let f : ℂ → ℝ≥0∞ := K.indicator (fun z => g (z : Sphere))
  have hf : Measurable f := (hg.comp OnePoint.continuous_coe.measurable).indicator hK.measurableSet
  have hfin : (∫⁻z, f z) < ∞ := by
    rw [lintegral_indicator hK.measurableSet]
    exact planar_density_on_compact_finite g hg henergy hK
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => f (Complex.equivRealProd.symm p)
  have hF : Measurable F := hf.comp Complex.measurableEquivRealProd.symm.measurable
  have hFfin : (∫⁻p, F p) < ∞ := by
    calc
      _ = ∫⁻z, f z :=
        (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).lintegral_comp hf
      _ < ∞ := hfin
  constructor
  · apply ae_lt_top hF.lintegral_prod_left'
    rw [← lintegral_prod_symm F hF.aemeasurable]
    exact hFfin.ne
  · apply ae_lt_top hF.lintegral_prod_right'
    rw [← lintegral_prod F hF.aemeasurable]
    exact hFfin.ne

end CircleDomainRigidity

end

end OAI

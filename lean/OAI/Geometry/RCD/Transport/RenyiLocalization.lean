import OAI.Geometry.RCD.Transport.RenyiMidpointCompression

namespace OAI

/-! # Localization of finite Rényi integrals

The reference measure is restricted only for compactness arguments. The
resulting values agree with the original Hausdorff-reference integrals,
including for supported measures which have a singular part.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem renyiPower_localized (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ᵐ x ∂ν, x∈B) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    Integrable (fun x => (ν.rnDeriv μ x).toReal^q) μ ∧
      (∫ x, (ν.rnDeriv μ x).toReal^q ∂μ) =
        ∫ x, (ν.rnDeriv (μ.restrict B) x).toReal^q ∂μ.restrict B := by
  have he := density_transform_eq_indicator μ ν hB hs (fun r => r^q)
    (Real.zero_rpow hq0.ne')
  have hr : (fun x => (ν.rnDeriv μ x).toReal^q) =ᵐ[μ.restrict B]
      fun x => (ν.rnDeriv (μ.restrict B) x).toReal^q := by
    filter_upwards [rnDeriv_restrict_reference μ ν hB] with x hx
    rw [hx]
  have hil := integrable_density_power (μ.restrict B) _
    (ν.measurable_rnDeriv (μ.restrict B)).ennreal_toReal Measure.integrable_toReal_rnDeriv
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hq0.le hq1
  have hir : Integrable (fun x => (ν.rnDeriv μ x).toReal^q) (μ.restrict B) := hil.congr hr.symm
  refine ⟨((integrable_indicator_iff hB).mpr hir).congr he.symm,?_⟩
  calc
    _ = ∫ x, B.indicator (fun x => (ν.rnDeriv μ x).toReal^q) x ∂μ := integral_congr_ae he
    _ = ∫ x, (ν.rnDeriv μ x).toReal^q ∂μ.restrict B := integral_indicator hB
    _ = _ := integral_congr_ae hr

theorem renyiIntegral_localized (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ᵐ x ∂ν, x∈B) {N : ℝ} (hN : 1 < N) :
    renyiIntegral μ ν N = renyiIntegral (μ.restrict B) ν N := by
  have hN0 : 0 < N := by linarith
  have hq0 : 0 < 1-1/N := sub_pos.mpr ((div_lt_one hN0).mpr hN)
  have hq1 : 1-1/N ≤ 1 := by have := one_div_pos.mpr hN0; linarith
  obtain ⟨hi,he⟩ := renyiPower_localized μ ν hB hs hq0 hq1
  have hil := integrable_density_power (μ.restrict B) _
    (ν.measurable_rnDeriv (μ.restrict B)).ennreal_toReal Measure.integrable_toReal_rnDeriv
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hq0.le hq1
  exact (rnDeriv_power_lintegral_eq_of_integrable μ ν hq0.le hi).trans
    ((congrArg ENNReal.ofReal he).trans
      (rnDeriv_power_lintegral_eq_of_integrable (μ.restrict B) ν hq0.le hil).symm)

end RegularPointCoordinates

end

end OAI

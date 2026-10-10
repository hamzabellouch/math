import OAI.Geometry.RCD.Transport.RenyiSemicontinuity

namespace OAI

/-! # Removing singular mass strictly improves the Rényi integral

The replacement measure retains the original absolutely continuous part
and adds a nonzero absolutely continuous measure. This handles possible
singular parts of an entropy-maximizing midpoint before any density bound.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem integral_rpow_add_strict (μ : Measure X) [IsFiniteMeasure μ]
    {ρ σ : X → ℝ} (hρ : Measurable ρ) (hσ : Measurable σ)
    (hiρ : Integrable ρ μ) (hiσ : Integrable σ μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x)
    (hσpos : 0 < ∫ x, σ x ∂μ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (∫ x, (ρ x)^q ∂μ) < ∫ x, (ρ x+σ x)^q ∂μ := by
  have hi0 := integrable_density_power μ ρ hρ hiρ (Eventually.of_forall hρ0) hq0.le hq1.le
  have hi1 := integrable_density_power μ (fun x => ρ x+σ x) (hρ.add hσ) (hiρ.add hiσ)
    (Eventually.of_forall fun x => add_nonneg (hρ0 x) (hσ0 x)) hq0.le hq1.le
  let d := fun x => (ρ x+σ x)^q-(ρ x)^q
  have hd0 (x : X) : 0 ≤ d x := sub_nonneg.mpr
    (Real.rpow_le_rpow (hρ0 x) (le_add_of_nonneg_right (hσ0 x)) hq0.le)
  have hdI : Integrable d μ := hi1.sub hi0
  have hsupport : Function.support σ ⊆ Function.support d := by
    intro x hx
    have hs : 0 < σ x := lt_of_le_of_ne (hσ0 x) (Ne.symm hx)
    exact ne_of_gt (sub_pos.mpr (Real.rpow_lt_rpow (hρ0 x) (by linarith) hq0))
  have hspos := (integral_pos_iff_support_of_nonneg hσ0 hiσ).mp hσpos
  have hdpos : 0 < ∫ x, d x ∂μ :=
    (integral_pos_iff_support_of_nonneg hd0 hdI).mpr (hspos.trans_le (measure_mono hsupport))
  change 0 < ∫ x, (ρ x+σ x)^q-(ρ x)^q ∂μ at hdpos
  rw [integral_sub hi1 hi0] at hdpos
  linarith

theorem renyi_singular_replacement_strict (μ ν η : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure η]
    (hη : η ≪ μ) (hηpos : 0 < η univ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (∫ x, (ν.rnDeriv μ x).toReal^q ∂μ) <
      ∫ x, ((ν-ν.singularPart μ+η).rnDeriv μ x).toReal^q ∂μ := by
  let ρ := fun x => (ν.rnDeriv μ x).toReal
  let σ := fun x => (η.rnDeriv μ x).toReal
  have hρ : Measurable ρ := (ν.measurable_rnDeriv μ).ennreal_toReal
  have hσ : Measurable σ := (η.measurable_rnDeriv μ).ennreal_toReal
  have hρ0 : ∀ x, 0 ≤ ρ x := fun _ => ENNReal.toReal_nonneg
  have hσ0 : ∀ x, 0 ≤ σ x := fun _ => ENNReal.toReal_nonneg
  have hnew : μ.withDensity (fun x => ENNReal.ofReal (ρ x+σ x)) = ν-ν.singularPart μ+η := by
    calc
      _ = μ.withDensity (fun x => ENNReal.ofReal (ρ x)+ENNReal.ofReal (σ x)) :=
        withDensity_congr_ae (Eventually.of_forall fun x => ENNReal.ofReal_add (hρ0 x) (hσ0 x))
      _ = μ.withDensity (fun x => ENNReal.ofReal (ρ x))+μ.withDensity (fun x => ENNReal.ofReal (σ x)) :=
        withDensity_add_left hρ.ennreal_ofReal (fun x => ENNReal.ofReal (σ x))
      _ = μ.withDensity (ν.rnDeriv μ)+η := by
        rw [withDensity_ofReal_rnDeriv μ η hη]
        congr 1
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
        exact ENNReal.ofReal_toReal hx.ne
      _ = _ := by rw [Measure.measure_sub_singularPart]
  have hrn : (fun x => ((ν-ν.singularPart μ+η).rnDeriv μ x).toReal) =ᵐ[μ]
      fun x => ρ x+σ x := by
    rw [←hnew]
    filter_upwards [Measure.rnDeriv_withDensity μ (hρ.add hσ).ennreal_ofReal] with x hx
    change (μ.withDensity (fun x => ENNReal.ofReal (ρ x+σ x))).rnDeriv μ x =
      ENNReal.ofReal (ρ x+σ x) at hx
    rw [hx,ENNReal.toReal_ofReal (add_nonneg (hρ0 x) (hσ0 x))]
  have hp : 0 < ∫ x, σ x ∂μ := by
    change 0 < ∫ x, (η.rnDeriv μ x).toReal ∂μ
    rw [Measure.integral_toReal_rnDeriv hη]
    exact ENNReal.toReal_pos hηpos.ne' (measure_ne_top η univ)
  have hh := integral_rpow_add_strict μ hρ hσ Measure.integrable_toReal_rnDeriv
    Measure.integrable_toReal_rnDeriv hρ0 hσ0 hp hq0 hq1
  exact hh.trans_eq (integral_congr_ae (hrn.fun_comp fun r => r^q)).symm

end RegularPointCoordinates

end

end OAI

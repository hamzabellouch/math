import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import OAI.Combinatorics.BalancedRyser.Profiles.DetectionThresholds
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileDetectionBridge

namespace OAI

open MeasureTheory Set Filter
open scoped Topology

namespace Balanced.ProfileParameterLaw

noncomputable def parameterLaw (γ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo 0 1)).withDensity (fun z : ℝ => ENNReal.ofReal (γ * z ^ (γ - 1)))

theorem parameterLaw_absolutelyContinuous (γ : ℝ) :
    parameterLaw γ ≪ volume.restrict (Ioo 0 1) :=
  withDensity_absolutelyContinuous _ _

theorem ae_parameterLaw_mem (γ : ℝ) :
    ∀ᵐ z : ℝ ∂parameterLaw γ, z ∈ Ioo 0 1 :=
  (parameterLaw_absolutelyContinuous γ).ae_le (ae_restrict_mem measurableSet_Ioo)

theorem ae_parameterLaw_of_ae {p : ℝ → Prop} (γ : ℝ)
    (hp : ∀ᵐ z : ℝ ∂volume.restrict (Ioo 0 1), p z) :
    ∀ᵐ z : ℝ ∂parameterLaw γ, p z :=
  (parameterLaw_absolutelyContinuous γ).ae_le hp

theorem parameterLaw_isProbabilityMeasure {γ : ℝ} (hγ : 0 < γ) :
    IsProbabilityMeasure (parameterLaw γ) := by
  have hi : IntegrableOn (fun z : ℝ => γ * z ^ (γ - 1)) (Ioo 0 1) volume := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < γ - 1)).const_mul γ
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo 0 1)] (fun z : ℝ => γ * z ^ (γ - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact mul_nonneg hγ.le (Real.rpow_nonneg hz.1.le _)
  have hint : (∫ z : ℝ in Ioo 0 1, γ * z ^ (γ - 1)) = 1 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < γ - 1))]
    simp [Real.zero_rpow hγ.ne', hγ.ne']
  constructor
  change (volume.restrict (Ioo 0 1)).withDensity _ univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hnonneg, hint]
  norm_num

@[simp] theorem parameterLaw_one : parameterLaw 1 = volume.restrict (Ioo 0 1) := by
  simp [parameterLaw]

theorem measurable_real_rpow_const (r : ℝ) : Measurable (fun z : ℝ => z ^ r) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro z hz
  exact (Real.continuousAt_rpow_const z r (Or.inl (by simpa using hz))).continuousWithinAt

theorem measurable_profileTest (w : ℕ × ℕ → ℝ) :
    Measurable (fun p : (ℕ × ℕ → ℝ) × ℝ => ∑' a, p.1 a * p.2 ^ w a) := by
  exact Measurable.tsum (fun a => ((measurable_pi_apply a).comp measurable_fst).mul
    ((measurable_real_rpow_const (w a)).comp measurable_snd))

theorem measurable_planeTest :
    Measurable (fun p : (ℕ × ℕ → ℝ) × ℝ => ProfileDetectionBridge.planeTest p.1 p.2) :=
  measurable_profileTest _

theorem measurable_dTest :
    Measurable (fun p : (ℕ × ℕ → ℝ) × ℝ => ProfileDetectionBridge.dTest p.1 p.2) :=
  measurable_profileTest _

theorem measurable_cTest :
    Measurable (fun p : (ℕ × ℕ → ℝ) × ℝ => ProfileDetectionBridge.cTest p.1 p.2) :=
  measurable_profileTest _

end Balanced.ProfileParameterLaw

end OAI

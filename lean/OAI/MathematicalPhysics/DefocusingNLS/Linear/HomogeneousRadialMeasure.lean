import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialL2
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace OAI

/-! # Exact radial Jacobian and Schwartz radial tests in dimension twelve -/

open MeasureTheory Set LineDeriv
open scoped SchwartzMap LineDeriv

namespace DefocusingNLS

/-- The polar radial measure is precisely r¹¹ dr, with no normalization factor. -/
theorem integral_physicalRadiusMeasure (F : ℝ → ℂ) :
    (∫ r : PhysicalPositiveRadius, F r ∂physicalRadiusMeasure) =
      ∫ r in Ioi (0 : ℝ), (r ^ (11 : ℕ) : ℝ) • F r := by
  change (∫ r : PhysicalPositiveRadius, F r ∂(volume.comap Subtype.val).withDensity
    (fun r : PhysicalPositiveRadius => ENNReal.ofReal (r.1 ^ (11 : ℕ)))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun r : PhysicalPositiveRadius => ENNReal.ofReal (r.1 ^ (11 : ℕ))) by
      fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  trans ∫ r : PhysicalPositiveRadius, (r.1 ^ (11 : ℕ)) • F r ∂volume.comap Subtype.val
  · apply integral_congr_ae
    filter_upwards [] with r
    rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) 11)]
  · exact integral_subtype_comap (s := Ioi (0 : ℝ)) (μ := volume) measurableSet_Ioi
      (fun r : ℝ => (r ^ (11 : ℕ)) • F r)

/-- Schwartz radial tests remain square-integrable against the polar Jacobian. -/
theorem memLp_radialSchwartz (ψ : 𝓢(ℝ, ℂ)) :
    MemLp (fun r : PhysicalPositiveRadius => ψ r) 2 physicalRadiusMeasure := by
  have hmeas : AEStronglyMeasurable (fun r : PhysicalPositiveRadius => ψ r)
      physicalRadiusMeasure :=
    (ψ.continuous.comp continuous_subtype_val).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  change Integrable (fun r : PhysicalPositiveRadius => ‖ψ r‖ ^ 2)
    ((volume.comap Subtype.val).withDensity
      (fun r : PhysicalPositiveRadius => ENNReal.ofReal (r.1 ^ (11 : ℕ))))
  apply (integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun r : PhysicalPositiveRadius => ENNReal.ofReal (r.1 ^ (11 : ℕ))) by
      fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hi : Integrable (fun r : ℝ => ‖r‖ ^ (11 : ℕ) * ‖ψ r‖ ^ 2) := by
    apply ((ψ.integrable_pow_mul volume 11).mul_const (SchwartzMap.seminorm ℝ 0 0 ψ)).mono'
      ((continuous_norm.pow 11).mul (ψ.continuous.norm.pow 2)).aestronglyMeasurable
    filter_upwards [] with r
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg r) 11) (sq_nonneg ‖ψ r‖))]
    calc
      ‖r‖ ^ 11 * ‖ψ r‖ ^ 2 = (‖r‖ ^ 11 * ‖ψ r‖) * ‖ψ r‖ := by ring
      _ ≤ (‖r‖ ^ 11 * ‖ψ r‖) * SchwartzMap.seminorm ℝ 0 0 ψ :=
        mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ ψ r) (by positivity)
  have hs : Integrable (fun r : PhysicalPositiveRadius => ‖r.1‖ ^ 11 * ‖ψ r.1‖ ^ 2)
      (volume.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal (s := Ioi (0 : ℝ)) measurableSet_Ioi).mp hi.integrableOn
  apply hs.congr
  filter_upwards [] with r
  simp only [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) 11), smul_eq_mul,
    Real.norm_of_nonneg (le_of_lt r.2)]

/-- A test supported on the positive half-line has the same full-line integral. -/
theorem integral_Ioi_eq_of_zero_nonpositive (F : ℝ → ℂ)
    (hF : ∀ r, r ≤ 0 → F r = 0) :
    (∫ r in Ioi (0 : ℝ), F r) = ∫ r, F r := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext r
  by_cases hr : 0 < r
  · simp [hr]
  · simp [hr, hF r (le_of_not_gt hr)]

/-- Absorb the twelve-dimensional radial Jacobian into a Schwartz test. -/
noncomputable def radialWeightedSchwartzTest (ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun r : ℝ => (r : ℂ) ^ (11 : ℕ)) ψ

@[simp] theorem radialWeightedSchwartzTest_apply (ψ : 𝓢(ℝ, ℂ)) (r : ℝ) :
    radialWeightedSchwartzTest ψ r = (r : ℂ) ^ (11 : ℕ) * ψ r := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (Complex.hasTemperateGrowth_ofReal.pow 11) ψ r

/-- The transposed radial derivative includes the exact Jacobian. -/
noncomputable def radialTransposedTest (N : ℕ) (ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  ∂^{fun _ : Fin N => (1 : ℝ)} (radialWeightedSchwartzTest ψ)

theorem tsupport_radialWeightedSchwartzTest_subset (ψ : 𝓢(ℝ, ℂ)) :
    tsupport (radialWeightedSchwartzTest ψ) ⊆ tsupport ψ := by
  apply closure_mono
  intro r hr
  contrapose! hr
  simp only [Function.mem_support, ne_eq] at hr ⊢
  simp [hr]

theorem tsupport_radialTransposedTest_subset (N : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    tsupport (radialTransposedTest N ψ) ⊆ tsupport ψ :=
  (SchwartzMap.tsupport_iteratedLineDerivOp_subset _ _).trans
    (tsupport_radialWeightedSchwartzTest_subset ψ)

end DefocusingNLS

end OAI

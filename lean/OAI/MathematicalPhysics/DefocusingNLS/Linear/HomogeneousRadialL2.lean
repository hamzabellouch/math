import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousAngularL2

namespace OAI

/-! # Completed radial derivative contractions in the exact radial measure -/

open MeasureTheory Set

namespace DefocusingNLS

noncomputable def radialTensorCoefficient (N : ℕ) (j : Fin N → Fin 12)
    (ω : PhysicalUnitSphere) : ℝ := ∏ i, (ω.1 (j i))

theorem continuous_radialTensorCoefficient (N : ℕ) (j : Fin N → Fin 12) :
    Continuous (radialTensorCoefficient N j) := by
  unfold radialTensorCoefficient
  fun_prop

theorem radialTensorCoefficient_abs_le (N : ℕ) (j : Fin N → Fin 12)
    (ω : PhysicalUnitSphere) : |radialTensorCoefficient N j ω| ≤ 1 := by
  have hnorm : ‖ω.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using ω.2
  unfold radialTensorCoefficient
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · intro i _
    positivity
  · intro i _
    simpa only [Real.norm_eq_abs, hnorm] using PiLp.norm_apply_le (ω.1) (j i)

/-- Multiplying an angular test by a radial tensor coefficient preserves L². -/
theorem memLp_radialTensor_test (N : ℕ) (j : Fin N → Fin 12)
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure) :
    MemLp (fun ω => (radialTensorCoefficient N j ω : ℂ) * h ω)
      2 physicalSphereMeasure := by
  apply hh.of_le ((Complex.continuous_ofReal.comp (continuous_radialTensorCoefficient N j)).aestronglyMeasurable.mul
    hh.aestronglyMeasurable)
  filter_upwards [] with ω
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (radialTensorCoefficient_abs_le N j ω)

/-- Remove the polar density: this is exactly square integrability with
respect to r^11 dr, on the positive real half-line. -/
theorem radial_weighted_integrable_of_memLp (f : ℝ → ℂ)
    (hf : MemLp (fun r : PhysicalPositiveRadius => f r) 2 physicalRadiusMeasure) :
    IntegrableOn (fun r : ℝ => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi 0) := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  change Integrable (fun r : PhysicalPositiveRadius => ‖f r‖ ^ 2)
    ((volume.comap Subtype.val).withDensity
      (fun r : PhysicalPositiveRadius => ENNReal.ofReal (r.1 ^ (11 : ℕ)))) at hi
  have hw := (integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun r : PhysicalPositiveRadius => ENNReal.ofReal (r.1 ^ (11 : ℕ))) by
      fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hi
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  convert hw using 1
  funext r
  simp only [Function.comp_def, ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) 11),
    smul_eq_mul]

/-- The contraction is formed after completing each Cartesian derivative.
Its angular coefficients are r^11-weighted L² functions. -/
noncomputable def homogeneousRadialAngularDerivative (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (u : HomogeneousY a N)
    (r : PhysicalPositiveRadius) : ℂ :=
  ∑ j : Fin N → Fin 12, ∫ ω, inner ℂ
    ((radialTensorCoefficient N j ω : ℂ) * h ω)
    (homogeneousPolarDerivative a N ha ha1 hk j u (ω, r)) ∂physicalSphereMeasure

theorem homogeneousRadialAngularDerivative_memLp (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ))
    (h : PhysicalUnitSphere → ℂ) (hh : MemLp h 2 physicalSphereMeasure)
    (u : HomogeneousY a N) :
    MemLp (homogeneousRadialAngularDerivative a N ha ha1 hk h u)
      2 physicalRadiusMeasure := by
  classical
  apply memLp_finsetSum
  intro j _
  exact homogeneousPolarDerivative_angular_memLp a N ha ha1 hk j _
    (memLp_radialTensor_test N j h hh) u

end DefocusingNLS

end OAI

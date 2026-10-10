import OAI.MeasureTheory.Falconer.Fourier.SpatialFourierSeparation

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter
open scoped ComplexConjugate

noncomputable def spatialPairPhase (s : ℝ) (ξ : Plane) (z : Plane × Plane) : ℂ :=
  spatialFourierPhase s ξ z.1 * conj (spatialFourierPhase s ξ z.2)

@[fun_prop] theorem spatialPairPhase_continuous (s : ℝ) :
    Continuous (fun p : Plane × (Plane × Plane) => spatialPairPhase s p.1 p.2) := by
  unfold spatialPairPhase spatialFourierPhase
  fun_prop

theorem spatialPairPhase_norm (s : ℝ) (ξ : Plane) (z : Plane × Plane) :
    ‖spatialPairPhase s ξ z‖ = 1 := by
  simp [spatialPairPhase, spatialFourierPhase_norm]

theorem spatialFourier_joint_integrable (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure (Plane × Plane)) [IsFiniteMeasure μ]
    (A : Plane × Plane → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    Integrable (fun p : Plane × (Plane × Plane) =>
      spatialFourierCoeff δ L hδ hL j p.1 * (spatialPairPhase s p.1 p.2 * A p.2))
      (volume.prod μ) := by
  have hm : AEStronglyMeasurable (fun p : Plane × (Plane × Plane) =>
      spatialFourierCoeff δ L hδ hL j p.1 * (spatialPairPhase s p.1 p.2 * A p.2))
      (volume.prod μ) :=
    (spatialFourierCoeff δ L hδ hL j).continuous.aestronglyMeasurable.comp_fst.mul
      ((spatialPairPhase_continuous s).aestronglyMeasurable.mul
        hA.aestronglyMeasurable.comp_snd)
  apply (((spatialFourierCoeff_integrable δ L hδ hL j).norm.comp_fst μ).mul_const C).mono' hm
  filter_upwards with p
  simp only [norm_mul, spatialPairPhase_norm, one_mul]
  exact mul_le_mul_of_nonneg_left (hb p.2) (norm_nonneg _)

theorem spatialFourier_integral_swap (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure (Plane × Plane)) [IsFiniteMeasure μ]
    (A : Plane × Plane → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    (∫ z, spatialAnnulusKernel δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z ∂μ) =
      ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
        ∫ z, spatialPairPhase s ξ z * A z ∂μ := by
  have he (z : Plane × Plane) :
      spatialAnnulusKernel δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z =
        ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ * (spatialPairPhase s ξ z * A z) := by
    rw [← spatialFourierSeparation, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp [spatialPairPhase]
    ring
  simp_rw [he]
  simpa only [integral_const_mul] using
    (integral_integral_swap (f := fun ξ z => spatialFourierCoeff δ L hδ hL j ξ *
      (spatialPairPhase s ξ z * A z))
      (spatialFourier_joint_integrable δ L hδ hL j s μ A hA hb)).symm

end PlanarFalconer

end OAI

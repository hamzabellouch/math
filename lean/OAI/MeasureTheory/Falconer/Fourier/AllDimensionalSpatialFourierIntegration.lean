import OAI.MeasureTheory.Falconer.Fourier.AllDimensionalSpatialFourierSeparation

namespace OAI

/-! # Fubini for the original pair measure and the actual all-dimensional spatial factors. This is the spatial separation used by osc:spatial-separation. -/

namespace Falconer
open MeasureTheory Filter
open scoped ComplexConjugate
variable {d : ℕ}

noncomputable def spatialPairPhase (s : ℝ) (ξ : Space d) (z : Space d × Space d) : ℂ :=
  spatialFourierPhase s ξ z.1 * conj (spatialFourierPhase s ξ z.2)

@[fun_prop] theorem spatialPairPhase_continuous (s : ℝ) :
    Continuous (fun p : Space d × (Space d × Space d) => spatialPairPhase s p.1 p.2) := by
  unfold spatialPairPhase spatialFourierPhase
  fun_prop

theorem spatialPairPhase_norm (s : ℝ) (ξ : Space d) (z : Space d × Space d) :
    ‖spatialPairPhase s ξ z‖ = 1 := by
  simp [spatialPairPhase, spatialFourierPhase_norm]

theorem spatialFourier_joint_integrable (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure (Space d × Space d)) [IsFiniteMeasure μ]
    (A : Space d × Space d → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    Integrable (fun p : Space d × (Space d × Space d) =>
      spatialFourierCoeff (d := d) δ L hδ hL j p.1 * (spatialPairPhase s p.1 p.2 * A p.2))
      (volume.prod μ) := by
  have hm : AEStronglyMeasurable (fun p : Space d × (Space d × Space d) =>
      spatialFourierCoeff (d := d) δ L hδ hL j p.1 * (spatialPairPhase s p.1 p.2 * A p.2))
      (volume.prod μ) :=
    (spatialFourierCoeff (d := d) δ L hδ hL j).continuous.aestronglyMeasurable.comp_fst.mul
      ((spatialPairPhase_continuous s).aestronglyMeasurable.mul
        hA.aestronglyMeasurable.comp_snd)
  apply (((spatialFourierCoeff_integrable δ L hδ hL j).norm.comp_fst μ).mul_const C).mono' hm
  filter_upwards with p
  simp only [norm_mul, spatialPairPhase_norm, one_mul]
  exact mul_le_mul_of_nonneg_left (hb p.2) (norm_nonneg _)

theorem spatialFourier_integral_swap (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure (Space d × Space d)) [IsFiniteMeasure μ]
    (A : Space d × Space d → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    (∫ z, spatialAnnulusKernel (d := d) δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z ∂μ) =
      ∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
        ∫ z, spatialPairPhase s ξ z * A z ∂μ := by
  have he (z : Space d × Space d) :
      spatialAnnulusKernel (d := d) δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z =
        ∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ * (spatialPairPhase s ξ z * A z) := by
    rw [← spatialFourierSeparation, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp [spatialPairPhase]
    ring
  simp_rw [he]
  simpa only [integral_const_mul] using
    (integral_integral_swap (f := fun ξ z => spatialFourierCoeff (d := d) δ L hδ hL j ξ *
      (spatialPairPhase s ξ z * A z))
      (spatialFourier_joint_integrable δ L hδ hL j s μ A hA hb)).symm


/-- The spatial factor needed after a stationary inverse term, separated into
bounded multipliers of the two original endpoints. -/
theorem spatialInverseDistance_integral_separation
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) {s : ℝ} (hs : 0 < s)
    (μ : Measure (Space d × Space d)) [IsFiniteMeasure μ]
    (hsep : ∀ᵐ z ∂μ, δ ≤ dist z.1 z.2 / s ∧ dist z.1 z.2 / s ≤ L)
    (A : Space d × Space d → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    (∫ z, (↑((dist z.1 z.2 / s)^j)⁻¹ : ℂ) * A z ∂μ) =
      ∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
        ∫ z, spatialPairPhase s ξ z * A z ∂μ := by
  apply Eq.trans _ (spatialFourier_integral_swap δ L hδ hL j s μ A hA hb)
  apply integral_congr_ae
  filter_upwards [hsep] with z hz
  have hn : ‖s⁻¹ • (z.1-z.2)‖ = dist z.1 z.2 / s := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs,dist_eq_norm,div_eq_inv_mul]
  rw [spatialAnnulusKernel_eq δ L hδ hL j (by simpa only [hn] using hz.1) (by simpa only [hn] using hz.2),hn,
    Complex.ofReal_inv]

end Falconer

end OAI

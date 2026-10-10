import OAI.Geometry.RCD.Heat.HeatGammaEnergyEstimate
import OAI.Geometry.RCD.Heat.HeatLaplacianContraction
import OAI.Geometry.RCD.Sobolev.GammaLpNorm

namespace OAI

/-! # Uniform energy bounds down to heat time zero -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_compact_uniform_slope {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (f : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic t ht f) x ≤
        (L : ℝ) * Real.exp |K| := by
  have he : -K * t ≤ |K| := calc
    -K * t ≤ |-K * t| := le_abs_self _
    _ = |K| * t := by rw [abs_mul, abs_neg, abs_of_pos ht]
    _ ≤ |K| := by nlinarith [abs_nonneg K]
  filter_upwards [hX.heat_compact_slope_bdd K n hn hφ hs p f hf t ht] with x hx
  exact hx.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) L.coe_nonneg)

theorem NoncollapsedRCD.heat_compact_uniform_gamma_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] φ)
    (d : Lp ℝ 2 (hausdorff n X)) (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      fun x => (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic u)) x) ^ 2) :
    let M := (L : ℝ) * Real.exp |K|
    energyForm (hausdorff n X) hX.quadratic G G ≤
      4 * |K| * (M * ‖u‖) ^ 2 + 8 * M ^ 2 * ‖d‖ ^ 2 := by
  let μ := hausdorff n X
  let F := heatSobolev μ hX.quadratic t ht (SobolevSpace.toLp μ hX.quadratic u)
  let M : ℝ≥0 := ⟨(L : ℝ) * Real.exp |K|, mul_nonneg L.coe_nonneg (Real.exp_pos _).le⟩
  let C : ℝ≥0 := M ^ 2
  have hF : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic F x ≤ M :=
    hX.heat_compact_uniform_slope hn hφ hs p _ hu.symm ht ht1
  have hGb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic G x| ≤ C := by
    filter_upwards [hG, hF,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic F)]
      with x hx hfx h0
    rw [hx, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0 hfx 2
  have hΓ := localGamma_memLp_of_bounded_gradient μ hX.quadratic F F M hF
  have hGeq : SobolevSpace.toLp μ hX.quadratic G = hΓ.toLp (localGamma μ hX.quadratic F F) := by
    apply Lp.ext
    filter_upwards [hG, hΓ.coeFn_toLp, localGamma_self μ hX.quadratic F] with x hx hy hz
    exact hx.trans (hz.symm.trans hy.symm)
  have hFn : ‖F‖ ≤ ‖u‖ := by
    simpa only [heatH1, dite_eq_left ht] using heatH1_norm_le μ hX.quadratic t u
  have hGn : ‖SobolevSpace.toLp μ hX.quadratic G‖ ≤ (M : ℝ) * ‖u‖ := by
    rw [hGeq]
    exact (gammaLp_norm_le μ hX.quadratic F F M hF hΓ).trans
      (mul_le_mul_of_nonneg_left hFn M.coe_nonneg)
  have hDn := heatTail_laplacian_norm_le μ hX.quadratic u d hd ht
  have hb := hX.heat_gamma_energy_estimate hn p _ ht G C M hG hGb hF
  have hGsq := pow_le_pow_left₀ (norm_nonneg (SobolevSpace.toLp μ hX.quadratic G)) hGn 2
  have hDsq := pow_le_pow_left₀ (norm_nonneg _) hDn 2
  have h1 := mul_le_mul_of_nonneg_left hGsq (show 0 ≤ 4 * |K| by positivity)
  have h2 := mul_le_mul_of_nonneg_left hDsq (show 0 ≤ 4 * ((C : ℝ) + (M : ℝ) ^ 2) by positivity)
  have hresult := hb.trans (add_le_add h1 h2)
  change energyForm μ hX.quadratic G G ≤
    4 * |K| * ((M : ℝ) * ‖u‖) ^ 2 +
      4 * ((M : ℝ) ^ 2 + (M : ℝ) ^ 2) * ‖d‖ ^ 2 at hresult
  change energyForm μ hX.quadratic G G ≤
    4 * |K| * ((M : ℝ) * ‖u‖) ^ 2 + 8 * (M : ℝ) ^ 2 * ‖d‖ ^ 2
  nlinarith only [hresult]

end RegularPointCoordinates

end

end OAI

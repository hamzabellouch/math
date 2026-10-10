import OAI.Geometry.RCD.Sobolev.CutoffErrorL1
import OAI.Geometry.RCD.Sobolev.HarmonicEnergyGradient

namespace OAI

/-! # Dimensionless bounds for the actual harmonic cutoff source -/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem harmonic_cutoff_scaled_L1 {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianInput hX) (hproduct : LocalPoissonGradientProductInput hX)
    {p : X} {R κ C V : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hcurv : κ * R ^ 2 ≤ 1) (hC : 0 ≤ C)
    (L : ℝ≥0) (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (32 * R)) (u i))
    (hgrad : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (32 * R)),
      localGamma (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u v)
        (sobolevColumnMap (hausdorff n X) hX.quadratic u v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2)
    {M : PositiveBilinearMeasure X (Euclidean n)}
    (G : ∀ v, LocalHarmonicEnergy (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic u) M κ p (4 * R) L v)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (3 * R / 8) C)
    (ψ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p R C)
    (hvol : (hausdorff n X).real (ball p R) ≤ V * R ^ n)
    (hvol2 : (hausdorff n X).real (closedBall p (2 * R)) ≤ V * (3 * R) ^ n)
    (v : Euclidean n) :
    let D := (L : ℝ) ^ 2 * ‖v‖ ^ 2
    R ^ 2 * (∫ x, |cutoffSourceDensity (hausdorff n X) hX.quadratic
      (G v).energy χ.sobolev χ.laplacian x| ∂hausdorff n X) ≤
      (64 * (D * C + C ^ 2) + 4 * D ^ 2 * (C / 2 + 1) * 3 ^ n) * V * R ^ n := by
  intro D
  let μ := hausdorff n X
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  let E := ∫ x in ball p R, localGamma μ hX.quadratic (G v).energy (G v).energy x ∂μ
  have hE := harmonic_energy_gradient_le hX hhessian hproduct hR hκ hK hC L u hu hgrad ψ v
    (G v).energy (ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (show R ≤ 2 * (4 * R) by linarith)) (G v).representative)
  change E ≤ 4 * D * (((C / R ^ 2) / 2 + κ) * D * μ.real (closedBall p (2 * R))) at hE
  have hE' : R ^ 2 * E ≤ 4 * D ^ 2 * (C / 2 + 1) * 3 ^ n * V * R ^ n := by
    calc
      _ ≤ R ^ 2 * (4 * D * (((C / R ^ 2) / 2 + κ) * D * μ.real (closedBall p (2 * R)))) :=
        mul_le_mul_of_nonneg_left hE (sq_nonneg _)
      _ = 4 * D ^ 2 * (C / 2 + κ * R ^ 2) * μ.real (closedBall p (2 * R)) := by
        field_simp [hR.ne']
      _ ≤ 4 * D ^ 2 * (C / 2 + 1) * μ.real (closedBall p (2 * R)) := by
        gcongr
      _ ≤ 4 * D ^ 2 * (C / 2 + 1) * (V * (3 * R) ^ n) :=
        mul_le_mul_of_nonneg_left hvol2 (by positivity)
      _ = _ := by rw [mul_pow]; ring
  have hb := χ.error_L1_le μ hX.quadratic (by positivity) hC (show 2 * (3 * R / 8) < R by linarith)
    (G v).energy (by simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using (G v).bounded)
  change (∫ x, |cutoffSourceDensity μ hX.quadratic (G v).energy χ.sobolev χ.laplacian x| ∂μ) ≤
    (D * (C / (3 * R / 8) ^ 2) + (C / (3 * R / 8)) ^ 2) * μ.real (ball p R) + E at hb
  calc
    _ ≤ R ^ 2 * ((D * (C / (3 * R / 8) ^ 2) + (C / (3 * R / 8)) ^ 2) * μ.real (ball p R) + E) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = (64 / 9 : ℝ) * (D * C + C ^ 2) * μ.real (ball p R) + R ^ 2 * E := by
      field_simp [hR.ne']; ring
    _ ≤ 64 * (D * C + C ^ 2) * μ.real (ball p R) + R ^ 2 * E := by
      gcongr; norm_num
    _ ≤ 64 * (D * C + C ^ 2) * (V * R ^ n) +
        4 * D ^ 2 * (C / 2 + 1) * 3 ^ n * V * R ^ n :=
      add_le_add (mul_le_mul_of_nonneg_left hvol (by positivity)) hE'
    _ = _ := by ring

/-- One coefficient controls all unit coordinate tests and their pairwise sums. -/
theorem harmonic_cutoff_uniform_L1 {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianInput hX) (hproduct : LocalPoissonGradientProductInput hX)
    {p : X} {R κ C V B : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hcurv : κ * R ^ 2 ≤ 1) (hC : 0 ≤ C) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (L : ℝ≥0) (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (32 * R)) (u i))
    (hgrad : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (32 * R)),
      localGamma (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u v)
        (sobolevColumnMap (hausdorff n X) hX.quadratic u v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2)
    {M : PositiveBilinearMeasure X (Euclidean n)}
    (G : ∀ v, LocalHarmonicEnergy (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic u) M κ p (4 * R) L v)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (3 * R / 8) C)
    (ψ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p R C)
    (hvol : (hausdorff n X).real (ball p R) ≤ V * R ^ n)
    (hvol2 : (hausdorff n X).real (closedBall p (2 * R)) ≤ V * (3 * R) ^ n)
    (v : Euclidean n) (hL : (L : ℝ) ^ 2 ≤ B) (hv : ‖v‖ ≤ 2) :
    let D := 4 * B
    R ^ 2 * (∫ x, |cutoffSourceDensity (hausdorff n X) hX.quadratic
      (G v).energy χ.sobolev χ.laplacian x| ∂hausdorff n X) ≤
      (64 * (D * C + C ^ 2) + 4 * D ^ 2 * (C / 2 + 1) * 3 ^ n) * V * R ^ n := by
  intro D
  have h := harmonic_cutoff_scaled_L1 hX hhessian hproduct hR hκ hK hcurv hC
    L u hu hgrad G χ ψ hvol hvol2 v
  have hD : (L : ℝ) ^ 2 * ‖v‖ ^ 2 ≤ D := by
    have hv2 : ‖v‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg v]
    calc
      _ ≤ B * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hL (sq_nonneg _)
      _ ≤ B * 4 := mul_le_mul_of_nonneg_left hv2 hB
      _ = D := by dsimp only [D]; ring
  have hcoef : 64 * ((L : ℝ) ^ 2 * ‖v‖ ^ 2 * C + C ^ 2) +
      4 * ((L : ℝ) ^ 2 * ‖v‖ ^ 2) ^ 2 * (C / 2 + 1) * 3 ^ n ≤
      64 * (D * C + C ^ 2) + 4 * D ^ 2 * (C / 2 + 1) * 3 ^ n := by
    gcongr
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hV) (pow_nonneg hR.le _))

end RegularPointCoordinates

end

end OAI

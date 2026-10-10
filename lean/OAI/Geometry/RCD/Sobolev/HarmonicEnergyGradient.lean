import OAI.Geometry.RCD.Sobolev.GradientProductInput
import OAI.Geometry.RCD.Sobolev.PoissonSpanLift
import OAI.Geometry.RCD.Sobolev.ResidualBochnerMass

namespace OAI

/-! # Energy-gradient control from the finite-span calculus

Appending two zero harmonic functions permits the already stated Poisson
Hessian and gradient-product inputs to be applied to a harmonic column.
The auxiliary full measure is bounded with an actual larger cutoff.
-/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem harmonic_energy_gradient_le {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianInput hX) (hproduct : LocalPoissonGradientProductInput hX)
    {p : X} {R κ C : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hC : 0 ≤ C)
    (L : ℝ≥0) (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (32 * R)) (u i))
    (hgrad : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (32 * R)),
      localGamma (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u v)
        (sobolevColumnMap (hausdorff n X) hX.quadratic u v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p R C)
    (v : Euclidean n) (g : SobolevSpace (hausdorff n X) hX.quadratic)
    (hrep : SobolevSpace.toLp (hausdorff n X) hX.quadratic g =ᵐ[
      (hausdorff n X).restrict (ball p R)]
        localGamma (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u v)
          (sobolevColumnMap (hausdorff n X) hX.quadratic u v)) :
    (∫ x in ball p R, localGamma (hausdorff n X) hX.quadratic g g x ∂hausdorff n X) ≤
      4 * ((L : ℝ) ^ 2 * ‖v‖ ^ 2) *
        (((C / R ^ 2) / 2 + κ) * ((L : ℝ) ^ 2 * ‖v‖ ^ 2) *
          (hausdorff n X).real (closedBall p (2 * R))) := by
  let μ := hausdorff n X
  let z : Fin 2 → SobolevSpace μ hX.quadratic := fun _ => 0
  let U := sobolevColumnMap μ hX.quadratic (poissonSpan μ hX.quadratic u z)
  let H : ℝ≥0 := ⟨((n + 2 : ℕ) : ℝ) * (L : ℝ), by positivity⟩
  have hz (i : Fin 2) : IsConstantLaplacianOn μ hX.quadratic (ball p (32 * R)) (z i) 0 := by
    exact (isConstantLaplacianOn_zero_iff μ hX.quadratic _ _).mpr
      (by
        intro φ hφ
        simpa only [zero_smul, zero_mul] using
          energyForm_smul_left μ hX.quadratic 0 (0 : SobolevSpace μ hX.quadratic) φ)
  have hzero : poissonSpanLaplacian n 0 = 0 := by
    ext w
    simp [poissonSpanLaplacian, Fin.sum_univ_add]
  have hU (w) : IsConstantLaplacianOn μ hX.quadratic (ball p (8 * (4 * R))) (U w) ((0 : Euclidean (n + 2) →ₗ[ℝ] ℝ) w) := by
    simpa only [show 8 * (4 * R) = 32 * R by ring, hzero] using
      poissonSpan_constant_laplacian μ hX.quadratic u z 0 hu hz w
  have hUG (w) : ∀ᵐ x ∂μ.restrict (ball p (8 * (4 * R))),
      localGamma μ hX.quadratic (U w) (U w) x ≤ (H : ℝ) ^ 2 * ‖w‖ ^ 2 := by
    rw [show 8 * (4 * R) = 32 * R by ring]
    apply poissonSpan_gradient μ hX.quadratic u z (L : ℝ)
    · intro i
      have hh := hgrad (EuclideanSpace.single i 1)
      simpa only [sobolevColumnMap_single, PiLp.norm_single, norm_one, one_pow,
        mul_one] using hh
    · intro i
      filter_upwards [ae_restrict_of_ae (localGamma_smul_left μ hX.quadratic 0
        (0 : SobolevSpace μ hX.quadratic) 0)] with x hx
      simp only [zero_smul, zero_mul] at hx
      change localGamma μ hX.quadratic 0 0 x ≤ (L : ℝ) ^ 2
      rw [hx]
      exact sq_nonneg _
  obtain ⟨M, hM, _, _⟩ := hhessian κ hκ hK p (4 * R) (by positivity) H U 0 hU hUG
  let w := poissonCoordinateLift v
  have hUw : U w = sobolevColumnMap μ hX.quadratic u v :=
    poissonSpanMap_lift μ hX.quadratic u z v
  have hwgrad : ∀ᵐ x ∂μ.restrict (ball p R),
      localGamma μ hX.quadratic (U w) (U w) x ≤ ((L : ℝ) * ‖v‖) ^ 2 := by
    rw [hUw]
    have hh := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (show R ≤ 32 * R by linarith)) (hgrad v)
    simpa only [mul_pow] using hh
  have hb := hproduct κ hκ hK p (4 * R) (by positivity) H U 0 hU hUG M hM
    R hR (by linarith) w w g (by simpa only [hUw] using hrep) 0
    ((L : ℝ) * ‖v‖) ((L : ℝ) * ‖v‖) (by positivity) (by positivity) hwgrad hwgrad
  simp only [zero_smul, sub_zero, LinearMap.zero_apply, mul_zero, sq, zero_mul] at hb
  have hclose : closedBall p (2 * R) ⊆ ball p (32 * R) :=
    closedBall_subset_ball (by linarith)
  have hmass := χ.mass_le_of_gradient μ hX.quadratic hR (show R < 4 * R by linarith)
    hC hκ (Classical.choice (hM w))
    (by rw [hUw]; exact ae_restrict_of_ae_restrict_of_subset hclose (hgrad v))
  rw [M.measure_real w (ball p R) measurableSet_ball] at hb
  have hmul := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ 4 * ((L : ℝ) ^ 2 * ‖v‖ ^ 2) by positivity)
  nlinarith only [hb, hmul]

end RegularPointCoordinates

end

end OAI

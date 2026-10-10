import OAI.Geometry.RCD.Sobolev.DistancePoissonFamily
import OAI.Geometry.RCD.Sobolev.HarmonicGradientConstruction

namespace OAI

/-! # Uniform gradient bounds for the constructed distance Poisson sequence -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem DistancePoissonFamily.value_bound
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {Q : QuadraticCheegerEnergy μ}
    {n : ℕ} {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
    (F : DistancePoissonFamily μ Q n κ B J C p r hr) (k : ℕ) :
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (F.replacement k) x| ≤
      max 8 B * (r k) ^ 2 := by
  have hpos : 0<r k := hr k
  let q := positiveSquaredDistance μ Q (by positivity : 0 ≤ 4 * r k) (F.cutoff k)
  have hqrep := positiveSquaredDistance_representative μ Q (by positivity : 0 ≤ 4 * r k) (F.cutoff k)
  filter_upwards [hqrep, F.height k,
    Lp.coeFn_sub (SobolevSpace.toLp μ Q q) (SobolevSpace.toLp μ Q (F.replacement k))]
    with x hqx hh hsub
  have hqbound := positiveSquaredDistanceValue_bounds μ Q (by positivity : 0 ≤ 4 * r k) (F.cutoff k) x
  have hq0 : 0 ≤ SobolevSpace.toLp μ Q q x := by rw [hqx]; exact hqbound.1
  have hq8 : SobolevSpace.toLp μ Q q x ≤ 8 * (r k) ^ 2 := by
    rw [hqx]
    nlinarith [hqbound.2]
  change 0 ≤ SobolevSpace.toLp μ Q (q - F.replacement k) x ∧
    SobolevSpace.toLp μ Q (q - F.replacement k) x ≤ B * (r k) ^ 2 at hh
  rw [map_sub, hsub, Pi.sub_apply] at hh
  have h8 := mul_le_mul_of_nonneg_right (le_max_left 8 B) (sq_nonneg (r k))
  have hB := mul_le_mul_of_nonneg_right (le_max_right 8 B) (sq_nonneg (r k))
  exact abs_le.mpr ⟨by linarith, by linarith⟩


/-- A single gradient constant works for every center and actual replacement,
including interior balls centered near the source center. -/
theorem NoncollapsedRCD.distance_poisson_family_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    [(hausdorff n X).Regular] (hK : K≤0) (p₀ : X) {κ B : ℝ} (hκ : 0≤κ) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ A : ℝ, 0<A ∧ ∀ (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0<r k) (J Cχ : ℝ)
      (F : DistancePoissonFamily (hausdorff n X) hX.quadratic n κ B J Cχ p r hr)
      (k : ℕ) (z : X), r k≤1 → dist z (p k)≤r k/4 → -1≤K*(r k/16)^2 →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball z (r k/4)),
        localGamma (hausdorff n X) hX.quadratic (F.replacement k) (F.replacement k) x≤(A*r k)^2 := by
  let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let _ := hX.separable
  have hscalar := hX.scalarBochner_nonpositive K n hn hK p₀
  have hess := hX.poisson_hessian_input_of_scalar hn hscalar
  have hgradient := hX.poissonGradientInput
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p₀)
    (hX.canonicalHeatKernel_coordinateBounds hn p₀) hess
  obtain ⟨C, hC, hbound⟩ := hgradient hn
  let G := 16 * max 8 B + ((n : ℝ) + 16 * κ) / 16
  have hG : 0 < G := by
    have hh := le_max_left (8 : ℝ) B
    dsimp only [G]
    positivity
  refine ⟨C * G, mul_pos (by linarith) hG, ?_⟩
  intro p r hr J Cχ F k z hs1 hdist hcurv
  let s := r k
  have hs : 0<s := hr k
  have hsub : 8 * (s / 16) + dist z (p k) ≤ s := by change dist z (p k) ≤ s / 4 at hdist; linarith
  have hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball z (8 * (s / 16)))
      (F.replacement k) ((n : ℝ) + κ * (4 * s) ^ 2) :=
    (F.laplacian k).mono (hausdorff n X) hX.quadratic measurableSet_ball (ball_subset_ball' hsub)
  have hv : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (8 * (s / 16))),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (F.replacement k) x| ≤ max 8 B * s ^ 2 :=
    ae_restrict_of_ae (F.value_bound k)
  have hh := hbound z (s / 16) (by positivity) hcurv (F.replacement k)
    ((n : ℝ) + κ * (4 * s) ^ 2) (max 8 B * s ^ 2)
    (mul_nonneg ((by norm_num : (0 : ℝ) ≤ 8).trans (le_max_left _ _)) (sq_nonneg s)) hf hv
  have ha0 : 0 ≤ (n : ℝ) + κ * (4 * s) ^ 2 := by positivity
  have ha : (n : ℝ) + κ * (4 * s) ^ 2 ≤ (n : ℝ) + 16 * κ := by
    have hs2 : s ^ 2 ≤ 1 := by change s ≤ 1 at hs1; nlinarith
    have hm := mul_le_mul_of_nonneg_left hs2 hκ
    nlinarith
  have hraw : max 8 B * s ^ 2 / (s / 16) +
      |(n : ℝ) + κ * (4 * s) ^ 2| * (s / 16) ≤ G * s := by
    rw [abs_of_nonneg ha0]
    have he : max 8 B * s ^ 2 / (s / 16) = 16 * max 8 B * s := by field_simp
    rw [he]
    dsimp only [G]
    have hm := mul_le_mul_of_nonneg_right ha (by positivity : 0 ≤ s / 16)
    nlinarith
  have hraw0 : 0 ≤ C * (max 8 B * s ^ 2 / (s / 16) +
      |(n : ℝ) + κ * (4 * s) ^ 2| * (s / 16)) := by
    have hm : 0 ≤ max (8 : ℝ) B := (by norm_num : (0 : ℝ) ≤ 8).trans (le_max_left _ _)
    positivity
  have hcomp : (C * (max 8 B * s ^ 2 / (s / 16) +
      |(n : ℝ) + κ * (4 * s) ^ 2| * (s / 16))) ^ 2 ≤ ((C * G) * s) ^ 2 := by
    apply (sq_le_sq₀ hraw0 (mul_nonneg (mul_pos (by linarith) hG).le hs.le)).mpr
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hraw (by linarith : 0 ≤ C)
  rw [show 4 * (s / 16) = s / 4 by ring] at hh
  exact hh.mono fun _ hx => hx.trans hcomp

end RegularPointCoordinates

end

end OAI

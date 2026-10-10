import OAI.Geometry.RCD.Sobolev.DirichletSobolevInput
import OAI.Geometry.RCD.Metric.DyadicDistanceSources

namespace OAI

/-! # Actual dyadic Poisson replacements with uniform constants -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

private theorem curvature_lower_bound_mono {K r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (hcurv : -1 ≤ K * R ^ 2) : -1 ≤ K * r ^ 2 := by
  by_cases hK : 0 ≤ K
  · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (mul_nonneg hK (sq_nonneg _))
  · have hsq : r ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hr (hr.trans hrR)).mpr hrR
    exact hcurv.trans (mul_le_mul_of_nonpos_left hsq (le_of_not_ge hK))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- These are actual solutions for the sources in `S`, not replacement
existence or error estimates supplied as additional assumptions. -/
structure DyadicDistanceReplacements {n : ℕ} {κ r0 : ℝ} {p : X}
    (S : DyadicDistanceSources μ hQ n κ p r0) (B J C : ℝ) where
  cutoff : ∀ i, GoodLaplacianCutoff μ hQ p (4 * distanceSourceRadius r0 i) C
  replacement : ℕ → SobolevSpace μ hQ
  boundary : ∀ i, replacement i - positiveSquaredDistance μ hQ
    (by have := distanceSourceRadius_pos S.radius_pos i; positivity) (cutoff i) ∈
      SobolevSpace.dirichlet μ hQ (ball p (distanceSourceRadius r0 i))
  laplacian : ∀ i, IsConstantLaplacianOn μ hQ (ball p (distanceSourceRadius r0 i))
    (replacement i) ((n : ℝ) + κ * (4 * distanceSourceRadius r0 i) ^ 2)
  height : ∀ i, ∀ᵐ x ∂μ,
    0 ≤ SobolevSpace.toLp μ hQ (positiveSquaredDistance μ hQ
      (by have := distanceSourceRadius_pos S.radius_pos i; positivity) (cutoff i) - replacement i) x ∧
    SobolevSpace.toLp μ hQ (positiveSquaredDistance μ hQ
      (by have := distanceSourceRadius_pos S.radius_pos i; positivity) (cutoff i) - replacement i) x ≤
        B * (distanceSourceRadius r0 i) ^ 2
  gradient_error : ∀ i,
    (∫ x in ball p (distanceSourceRadius r0 i), SobolevSpace.minimalSlope μ hQ
      (positiveSquaredDistance μ hQ
        (by have := distanceSourceRadius_pos S.radius_pos i; positivity) (cutoff i) - replacement i) x ∂μ) ≤
      (S.source i).real (ball p (distanceSourceRadius r0 i)) * distanceSourceRadius r0 i * J
  energy_error : ∀ i,
    (∫ x, (SobolevSpace.minimalSlope μ hQ
      (positiveSquaredDistance μ hQ
        (by have := distanceSourceRadius_pos S.radius_pos i; positivity) (cutoff i) - replacement i) x) ^ 2 ∂μ) ≤
      (S.source i).real (ball p (distanceSourceRadius r0 i)) * (B * (distanceSourceRadius r0 i) ^ 2)
  density_error : ∀ i,
    (∫ x in ball p (distanceSourceRadius r0 i),
      |(1 / 2 : ℝ) * localGamma μ hQ (replacement i) (replacement i) x -
        (1 / 2 : ℝ) * localGamma μ hQ
          (positiveSquaredDistance μ hQ
            (by have := distanceSourceRadius_pos S.radius_pos i; positivity) (cutoff i))
          (positiveSquaredDistance μ hQ
            (by have := distanceSourceRadius_pos S.radius_pos i; positivity) (cutoff i)) x| ∂μ) ≤
      (J + B / 2) * (distanceSourceRadius r0 i) ^ 2 *
        (S.source i).real (ball p (distanceSourceRadius r0 i))

omit [IsFiniteMeasureOnCompacts μ] in
/-- The constants precede the center, root radius and selected source
family, allowing the same constants in the two-center radial argument. -/
theorem dyadic_distance_replacements_of_published {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hsobolev : LocalDirichletSobolevInput hX) (hcutoff : LocalGoodCutoffInput hX)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ B J Cχ : ℝ, 0 < B ∧ 0 < J ∧ 1 ≤ Cχ ∧ ∀ (p : X) (r0 : ℝ)
      (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0),
      r0 ≤ 1 →
      (∀ i, -1 ≤ K * (64 * distanceSourceRadius r0 i) ^ 2) →
      (∀ i, 0 < (hausdorff n X).real (ball p (distanceSourceRadius r0 i))) →
      (∀ i, 2 * (hausdorff n X).real (ball p (distanceSourceRadius r0 i)) ≤
        (hausdorff n X).real (ball p (2 * distanceSourceRadius r0 i))) →
      Nonempty (DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J Cχ) := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨d, C, hd, hC, hsob⟩ := hsobolev hn
  obtain ⟨Cχ, hCχ, hχ⟩ := hcutoff hn
  obtain ⟨H, hH, hsolve⟩ := normalized_distance_poisson_estimates (hausdorff n X) hX.quadratic hd hC
  let B := 1 / 2 + ((n : ℝ) + 16 * κ) * H
  let J := Real.sqrt (balancedGradientConstant d ((1 + d) / 2) * C)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hJ : 0 < J := Real.sqrt_pos.mpr
    (mul_pos (balancedGradientConstant_pos (by linarith) (by linarith)) hC)
  refine ⟨B, J, Cχ, hB, hJ, hCχ, ?_⟩
  intro p r0 S hr01 hcurv hvol hdouble
  have hex (i : ℕ) : ∃ χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p
      (4 * distanceSourceRadius r0 i) Cχ,
      ∃ f : SobolevSpace (hausdorff n X) hX.quadratic,
        let q := positiveSquaredDistance (hausdorff n X) hX.quadratic
          (by have := distanceSourceRadius_pos S.radius_pos i; positivity) χ
        f - q ∈ SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p (distanceSourceRadius r0 i)) ∧
        IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (distanceSourceRadius r0 i)) f
          ((n : ℝ) + κ * (4 * distanceSourceRadius r0 i) ^ 2) ∧
        (∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic (q - f) x ∧
          SobolevSpace.toLp (hausdorff n X) hX.quadratic (q - f) x ≤ B * (distanceSourceRadius r0 i) ^ 2) ∧
        (∫ x in ball p (distanceSourceRadius r0 i),
          SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (q - f) x ∂hausdorff n X) ≤
          (S.source i).real (ball p (distanceSourceRadius r0 i)) * distanceSourceRadius r0 i * J ∧
        (∫ x, (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (q - f) x) ^ 2 ∂hausdorff n X) ≤
          (S.source i).real (ball p (distanceSourceRadius r0 i)) * (B * (distanceSourceRadius r0 i) ^ 2) ∧
        (∫ x in ball p (distanceSourceRadius r0 i),
          |(1 / 2 : ℝ) * localGamma (hausdorff n X) hX.quadratic f f x -
            (1 / 2 : ℝ) * localGamma (hausdorff n X) hX.quadratic q q x| ∂hausdorff n X) ≤
          (J + B / 2) * (distanceSourceRadius r0 i) ^ 2 *
            (S.source i).real (ball p (distanceSourceRadius r0 i)) := by
    let r := distanceSourceRadius r0 i
    have hr : 0 < r := distanceSourceRadius_pos S.radius_pos i
    have hrle : r ≤ 1 := by
      have ho := distanceSourceRadius_outer_le S.radius_pos.le i
      change 2 * r ≤ r0 at ho
      linarith
    have h4 := curvature_lower_bound_mono (by positivity : 0 ≤ 4 * r) (by linarith : 4 * r ≤ 64 * r) (hcurv i)
    obtain ⟨χ⟩ := hχ p (4 * r) (by positivity) h4
    let _ := S.finite i
    have hpoin := hX.annular_dirichlet_poincare hn p hr hrle (hvol i) (hdouble i)
    have hsource := positiveSquaredDistance_source (hausdorff n X) hX.quadratic
      (by positivity : 0 ≤ 4 * r) χ (by linarith : r ≤ 4 * r) (S.source i) (S.defect i)
    obtain ⟨f, hfq, hf, hh, hg, he, hdens⟩ := hsolve p r (4 * r) Cχ (by positivity) χ
      hr (by linarith) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (hvol i)
      (annularPoincareConstant K n * r ^ 2) (mul_nonneg (annularPoincareConstant_pos K n).le (sq_nonneg r))
      hpoin (hsob p r hr (hcurv i) (hdouble i)) (S.eikonal i)
      ((n : ℝ) + κ * (4 * r) ^ 2) (by positivity) (S.source i) (S.finite i) hsource
    have haB : 1 / 2 + ((n : ℝ) + κ * (4 * r) ^ 2) * H ≤ B := by
      have hrsq : r ^ 2 ≤ 1 := by nlinarith
      have hb := mul_le_mul_of_nonneg_left hrsq hκ
      dsimp only [B]
      nlinarith
    have hmass : 0 ≤ (S.source i).real (ball p r) := measureReal_nonneg
    refine ⟨χ, f, hfq, hf, ?_, hg, ?_, ?_⟩
    · exact hh.mono fun x hx => ⟨hx.1, hx.2.trans (mul_le_mul_of_nonneg_right haB (sq_nonneg r))⟩
    · exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right haB (sq_nonneg r)) hmass)
    · exact hdens.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (add_le_add (le_refl J)
          (div_le_div_of_nonneg_right haB (by norm_num : (0 : ℝ) ≤ 2)))
          (sq_nonneg r)) hmass)
  choose χ f hfq hf hh hg he hdens using hex
  exact ⟨⟨χ, f, hfq, hf, hh, hg, he, hdens⟩⟩

end RegularPointCoordinates

end

end OAI

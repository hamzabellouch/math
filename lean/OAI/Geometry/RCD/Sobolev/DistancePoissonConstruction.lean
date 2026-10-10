import OAI.Geometry.RCD.Harmonic.DyadicDistanceReplacements
import OAI.Geometry.RCD.Sobolev.DirichletSobolevConstruction
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent

namespace OAI

/-! # Uniform actual Poisson replacements for arbitrary distance sources

Only one radius at each center is needed by the near-regular limit argument.
The same constants work simultaneously for every such center and source.
-/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

private theorem distance_curvature_lower {K r R : ℝ} (hr : 0≤r) (hrR : r≤R)
    (hcurv : -1≤K*R^2) : -1≤K*r^2 := by
  by_cases hK : 0≤K
  · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg _))
  · have hsq : r^2≤R^2 := (sq_le_sq₀ hr (hr.trans hrR)).mpr hrR
    exact hcurv.trans (mul_le_mul_of_nonpos_left hsq (le_of_not_ge hK))

theorem NoncollapsedRCD.uniform_distance_poisson_replacement {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {κ : ℝ} (hκ : 0≤κ) :
    let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    ∃ B J Cχ : ℝ, 0<B ∧ 0<J ∧ 1≤Cχ ∧ ∀ (p : X) (r : ℝ) (hr : 0<r),
      r≤1 → -1≤K*(64*r)^2 → 0<(hausdorff n X).real (ball p r) →
      2*(hausdorff n X).real (ball p r)≤(hausdorff n X).real (ball p (2*r)) →
      ∀ (σ : Measure X), IsFiniteMeasure σ →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (4*r)),
        localGamma (hausdorff n X) hX.quadratic
          (inwardSobolev (hausdorff n X) hX.quadratic p (4*r))
          (inwardSobolev (hausdorff n X) hX.quadratic p (4*r)) x=1) →
      (∀ χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (4*r) Cχ,
        ∀ (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (L : ℝ≥0),
          LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball p r →
          SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
          energyForm (hausdorff n X) hX.quadratic
            (positiveSquaredDistance (hausdorff n X) hX.quadratic (mul_nonneg (by norm_num) hr.le) χ) ψ+
            ((n:ℝ)+κ*(4*r)^2)*(∫ x in ball p r, v x ∂hausdorff n X)=∫ x, v x ∂σ) →
      ∃ (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (4*r) Cχ)
        (f : SobolevSpace (hausdorff n X) hX.quadratic),
        let q := positiveSquaredDistance (hausdorff n X) hX.quadratic (mul_nonneg (by norm_num) hr.le) χ
        f-q ∈ SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p r) ∧
        IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p r) f ((n:ℝ)+κ*(4*r)^2) ∧
        (∀ᵐ x ∂hausdorff n X, 0≤SobolevSpace.toLp (hausdorff n X) hX.quadratic (q-f) x ∧
          SobolevSpace.toLp (hausdorff n X) hX.quadratic (q-f) x≤B*r^2) ∧
        (∫ x in ball p r, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (q-f) x ∂hausdorff n X)
          ≤σ.real (ball p r)*r*J ∧
        (∫ x, (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (q-f) x)^2 ∂hausdorff n X)
          ≤σ.real (ball p r)*(B*r^2) ∧
        (∫ x in ball p r, |(1/2:ℝ)*localGamma (hausdorff n X) hX.quadratic f f x-
          (1/2:ℝ)*localGamma (hausdorff n X) hX.quadratic q q x| ∂hausdorff n X)
          ≤(J+B/2)*r^2*σ.real (ball p r) := by
  let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  dsimp only
  obtain ⟨d, C, hd, hC, hsob⟩ := hX.localDirichletSobolevInput hn
  obtain ⟨Cχ, hCχ, hχ⟩ := hX.goodCutoffInput hn
  obtain ⟨H, hH, hsolve⟩ := normalized_distance_poisson_estimates (hausdorff n X) hX.quadratic hd hC
  let B := 1 / 2 + ((n : ℝ) + 16 * κ) * H
  let J := Real.sqrt (balancedGradientConstant d ((1 + d) / 2) * C)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hJ : 0 < J := Real.sqrt_pos.mpr
    (mul_pos (balancedGradientConstant_pos (by linarith) (by linarith)) hC)
  refine ⟨B, J, Cχ, hB, hJ, hCχ, ?_⟩
  intro p r hr hrle hcurv hvol hdouble σ hσ heik hsource
  have h4 := distance_curvature_lower (by positivity : 0 ≤ 4 * r) (by linarith : 4 * r ≤ 64 * r) hcurv
  obtain ⟨χ⟩ := hχ p (4 * r) (by positivity) h4
  let _ := hσ
  have hpoin := hX.annular_dirichlet_poincare hn p hr hrle hvol hdouble
  obtain ⟨f, hfq, hf, hh, hg, he, hdens⟩ := hsolve p r (4 * r) Cχ (by positivity) χ
    hr (by linarith) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hvol
    (annularPoincareConstant K n * r ^ 2) (mul_nonneg (annularPoincareConstant_pos K n).le (sq_nonneg r))
    hpoin (hsob p r hr hcurv hdouble) heik
    ((n : ℝ) + κ * (4 * r) ^ 2) (by positivity) σ hσ (hsource χ)
  have haB : 1 / 2 + ((n : ℝ) + κ * (4 * r) ^ 2) * H ≤ B := by
    have hrsq : r ^ 2 ≤ 1 := by nlinarith
    have hb := mul_le_mul_of_nonneg_left hrsq hκ
    dsimp only [B]
    nlinarith
  have hmass : 0 ≤ σ.real (ball p r) := measureReal_nonneg
  refine ⟨χ, f, hfq, hf, ?_, hg, ?_, ?_⟩
  · exact hh.mono fun x hx => ⟨hx.1, hx.2.trans (mul_le_mul_of_nonneg_right haB (sq_nonneg r))⟩
  · exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right haB (sq_nonneg r)) hmass)
  · exact hdens.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (add_le_add (le_refl J)
        (div_le_div_of_nonneg_right haB (by norm_num : (0 : ℝ) ≤ 2)))
        (sq_nonneg r)) hmass)

end RegularPointCoordinates

end

end OAI

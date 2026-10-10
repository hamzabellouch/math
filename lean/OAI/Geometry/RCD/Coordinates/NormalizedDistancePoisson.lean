import OAI.Geometry.RCD.Sobolev.PositiveDistancePoisson
import OAI.Geometry.RCD.Coordinates.NormalizedPoissonEstimates
import OAI.Geometry.RCD.Coordinates.NormalizedTorsion

namespace OAI

/-! # Uniform scale-correct Poisson replacement of squared distance -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- One torsion constant works for every center, radius and full positive
source. The height, gradient and energy-density errors have the exact
radius factors needed by the dyadic radial argument. -/
theorem normalized_distance_poisson_estimates {d C : ℝ} (hd : 1 < d) (hC : 0 < C) :
    ∃ H : ℝ, 0 < H ∧ ∀ (p : X) (r R D : ℝ) (hR : 0 ≤ R),
    ∀ χ : GoodLaplacianCutoff μ hQ p R D,
      0 < r → r ≤ R → μ (ball p r) ≠ ∞ → 0 < μ.real (ball p r) →
      ∀ P : ℝ, 0 ≤ P →
      (∀ φ : SobolevSpace.dirichlet μ hQ (ball p r),
        ‖SobolevSpace.toLp μ hQ φ.val‖ ^ 2 ≤ P * energyForm μ hQ φ.val φ.val) →
      (∀ φ : SobolevSpace.dirichlet μ hQ (ball p r),
        (∫ x in ball p r, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
          (C * r ^ 2 * (μ.real (ball p r)) ^ (1 / d - 1)) * energyForm μ hQ φ.val φ.val) →
      (∀ᵐ x ∂μ.restrict (ball p R),
        localGamma μ hQ (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p R) x = 1) →
      ∀ (a : ℝ), 0 ≤ a → ∀ (σ : Measure X), ∀ _hσ : IsFiniteMeasure σ,
      let q := positiveSquaredDistance μ hQ hR χ
      (∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (L : ℝ≥0),
        LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball p r →
        SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
        energyForm μ hQ q ψ + a * (∫ x in ball p r, v x ∂μ) = ∫ x, v x ∂σ) →
      ∃ f : SobolevSpace μ hQ,
        f - q ∈ SobolevSpace.dirichlet μ hQ (ball p r) ∧
        IsConstantLaplacianOn μ hQ (ball p r) f a ∧
        (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (q - f) x ∧
          SobolevSpace.toLp μ hQ (q - f) x ≤ (1 / 2 + a * H) * r ^ 2) ∧
        (∫ x in ball p r, SobolevSpace.minimalSlope μ hQ (q - f) x ∂μ) ≤
          σ.real (ball p r) * r * Real.sqrt (balancedGradientConstant d ((1 + d) / 2) * C) ∧
        (∫ x, (SobolevSpace.minimalSlope μ hQ (q - f) x) ^ 2 ∂μ) ≤
          σ.real (ball p r) * ((1 / 2 + a * H) * r ^ 2) ∧
        (∫ x in ball p r, |(1 / 2 : ℝ) * localGamma μ hQ f f x -
          (1 / 2 : ℝ) * localGamma μ hQ q q x| ∂μ) ≤
          (Real.sqrt (balancedGradientConstant d ((1 + d) / 2) * C) +
            (1 / 2 + a * H) / 2) * r ^ 2 * σ.real (ball p r) := by
  obtain ⟨H, hH, htor⟩ := exists_uniform_normalized_bounded_torsion μ hQ hd hC.le
  refine ⟨H, hH, ?_⟩
  intro p r R D hR χ hr hrR hfin hvol P hP hpoin hsob heik a ha σ hσ q hsource
  let _ := hσ
  have hsub : ball p r ⊆ ball p R := ball_subset_ball hrR
  obtain ⟨τ, hτ, hτbound⟩ := htor (ball p r) measurableSet_ball hfin hvol (r ^ 2)
    (sq_pos_of_pos hr) P hP hpoin hsob
  obtain ⟨f, hfq, hsolve⟩ := exists_constant_laplacian_replacement μ hQ (ball p r)
    measurableSet_ball hfin hP hpoin a q
  obtain ⟨L, hL⟩ := positiveSquaredDistanceValue_lipschitz μ hQ hR χ
  have hrep := positiveSquaredDistance_representative μ hQ hR χ
  have hnonneg : ∀ x, 0 ≤ positiveSquaredDistanceValue μ hQ χ x :=
    fun x => (positiveSquaredDistanceValue_bounds μ hQ hR χ x).1
  have hqbound : ∀ᵐ x ∂μ.restrict (ball p r), positiveSquaredDistanceValue μ hQ χ x ≤ r ^ 2 / 2 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [positiveSquaredDistanceValue_on_ball μ hQ χ (hsub hx)]
    have hdist : dist p x < r := by simpa only [mem_ball, dist_comm] using hx
    nlinarith [dist_nonneg (x := p) (y := x)]
  have hgrad : ∀ᵐ x ∂μ.restrict (ball p r), SobolevSpace.minimalSlope μ hQ q x ≤ r := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (positiveSquaredDistance_gradient μ hQ hR χ heik),
      ae_restrict_of_ae (localGamma_self μ hQ q), ae_restrict_mem measurableSet_ball]
      with x hγ hself hx
    change localGamma μ hQ q q x = dist p x ^ 2 at hγ
    have hdist : dist p x < r := by simpa only [mem_ball, dist_comm] using hx
    rw [hself] at hγ
    nlinarith [dist_nonneg (x := p) (y := x)]
  have hb := normalized_poisson_source_estimates μ hQ (ball p r) measurableSet_ball hfin hvol
    hP hpoin q f (positiveSquaredDistanceValue μ hQ χ) hL hnonneg hrep ha
    (by positivity) (mul_nonneg hH.le (sq_nonneg r)) hr.le hd hC (sq_pos_of_pos hr)
    hqbound hgrad τ hτ (hτbound.mono fun _ hx => hx.2) hfq hsolve σ hsource hsob
  have hheight : r ^ 2 / 2 + a * (H * r ^ 2) = (1 / 2 + a * H) * r ^ 2 := by ring
  have hroot : Real.sqrt (balancedGradientConstant d ((1 + d) / 2) * C * r ^ 2) =
      r * Real.sqrt (balancedGradientConstant d ((1 + d) / 2) * C) := by
    rw [Real.sqrt_mul (mul_nonneg (balancedGradientConstant_pos (by linarith) (by linarith)).le hC.le),
      Real.sqrt_sq_eq_abs, abs_of_pos hr, mul_comm]
  dsimp only at hb
  rw [hheight, hroot] at hb
  refine ⟨f, hfq, ?_, hb.1, ?_, hb.2.2.2.1, ?_⟩
  · intro φ hφ
    exact hsolve ⟨φ, hφ⟩
  · simpa only [mul_assoc] using hb.2.2.1
  · exact hb.2.2.2.2.trans_eq (by congr 1; ring)

end RegularPointCoordinates

end

end OAI

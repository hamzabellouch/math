import OAI.Geometry.RCD.Sobolev.ActualRadialEnergy

namespace OAI

/-! # Interior radial energy in the same normalizing covector frame -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem LocalHessianPairing.cast_right_mixed (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {s : Set X} {f a a' : SobolevSpace μ hQ} (ha : a = a')
    (G : LocalHessianPairing μ hQ s f a) :
    (ha ▸ G : LocalHessianPairing μ hQ s f a').mixed = G.mixed := by
  cases ha
  rfl

/-- Applying the energy estimate in a normalized coordinate frame keeps
its source term in the inverse-frame norm of the original covector. The
radial function and the fitted affine function remain the original ones. -/
theorem framed_radial_fit_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianInput hX) (hgradient : LocalHarmonicL2GradientInput hX)
    (hn : 2 ≤ n) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧ ∀ {κ r0 B J C A ε Cχ Lbase : ℝ},
      0 ≤ κ → -κ ≤ K → 0 ≤ B → 0 ≤ J → 0 ≤ A → 0 ≤ ε → 0 ≤ Cχ →
      ∀ (p : X) (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0)
        (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C) (i : ℕ),
      distanceSourceRadius r0 i ≤ 1 → -κ₀ ≤ K * (distanceSourceRadius r0 i / 64) ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (N : Euclidean n ≃L[ℝ] Euclidean n),
      (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
        (ball p (distanceSourceRadius r0 i / 4)) (transformedColumn (hausdorff n X) hX.quadratic u N j)) →
      ∀ _hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
        localGamma (hausdorff n X) hX.quadratic (transformedColumn (hausdorff n X) hX.quadratic u N j) (transformedColumn (hausdorff n X) hX.quadratic u N j) x ≤ (1 + ε) ^ 2,
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
        localGamma (hausdorff n X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
          (A * distanceSourceRadius r0 i) ^ 2) →
      ∀ _χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ,
      0 < (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)) →
      2 * (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)) ≤
        (hausdorff n X).real (ball p (2 * (distanceSourceRadius r0 i / 64))) →
      ∀ hbase : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 64)),
        localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ Lbase ^ 2,
      ∀ b : Euclidean n,
      let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let r := s / 64
      let hcoord := gamma_column_le_of_diagonal_bounds μ hX.quadratic u (ball p r) Lbase hbase b
      ∃ G : LocalHessianPairing μ hX.quadratic (ball p r) (T.replacement i)
        (sobolevColumnMap μ hX.quadratic u b),
      ∀ (F : SobolevSpace μ hX.quadratic) {I : ℝ},
      IsSobolevHarmonicOn μ hX.quadratic (ball p r) F →
      ‖radialPairingLp μ hX.quadratic (ball p r) (T.distanceDatum μ hX.quadratic i)
        (sobolevColumnMap μ hX.quadratic u b) hcoord - SobolevSpace.restrictLp μ hX.quadratic (ball p r) F‖ ^ 2 ≤ I →
      (∫ x in ball p (r / 2), localGamma μ hX.quadratic (G.mixed - F) (G.mixed - F) x ∂μ) ≤
        radialEnergyConstant K n Cg ε A B J Cχ *
          (I / r ^ 2 + (s ^ (n : ℝ) * normalizedPoissonDefect μ hX.quadratic S i) * ‖N.symm b‖ ^ 2) := by
  obtain ⟨Cg, hCg, he⟩ := actual_radial_fit_energy hX hhessian hgradient hn hκ₀
  refine ⟨Cg, hCg, ?_⟩
  intro κ r0 B J C A ε Cχ Lbase hκ hK hB hJ hA hε hCχ p S T i hs1 hcurv u N hu hgrad hf χ hvol hdouble hbase b
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hh := he hκ hK hB hJ hA hε hCχ p S T i hs1 hcurv
    (transformedColumn μ hQ u N) hu hgrad hf χ hvol hdouble (N.symm b)
  dsimp only at hh
  have hc : sobolevColumnMap μ hQ (transformedColumn μ hQ u N) (N.symm b) =
      sobolevColumnMap μ hQ u b := by
    rw [sobolevColumnMap_transformed]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨G, hG⟩ := hh
  let G' : LocalHessianPairing μ hQ (ball p (distanceSourceRadius r0 i / 64))
      (T.replacement i) (sobolevColumnMap μ hQ u b) := hc ▸ G
  refine ⟨G', ?_⟩
  intro H I hH hfit
  have hsub : ball p (distanceSourceRadius r0 i / 64) ⊆
      ball p (distanceSourceRadius r0 i / 4) := by
    apply ball_subset_ball
    have hs := distanceSourceRadius_pos S.radius_pos i
    linarith
  have haN := gamma_column_le_of_diagonal_bounds μ hQ (transformedColumn μ hQ u N)
    (ball p (distanceSourceRadius r0 i / 64)) (1 + ε)
    (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hgrad j)) (N.symm b)
  have haO := gamma_column_le_of_diagonal_bounds μ hQ u
    (ball p (distanceSourceRadius r0 i / 64)) Lbase hbase b
  have hraw := radialPairingLp_frame μ hQ u (ball p (distanceSourceRadius r0 i / 64))
    (T.distanceDatum μ hQ i) N b haN haO
  have hb := hG H hH (by rw [hraw]; exact hfit)
  have hmix : G'.mixed = G.mixed := LocalHessianPairing.cast_right_mixed μ hQ hc G
  rw [hmix]
  exact hb

end RegularPointCoordinates

end

end OAI

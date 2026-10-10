import OAI.Geometry.RCD.Coordinates.RegularPairPinching
import OAI.Geometry.RCD.Harmonic.MeanGramInverse
import OAI.Geometry.RCD.Coordinates.FrozenNorms

namespace OAI

/-! # Directional pinching for the canonical inverse mean Gram -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The mean normalization in the mass estimate is on the existing dyadic
sequence, fifteen indices after the source index. -/
theorem pinching_mean_radius (r : ℝ) (i : ℕ) :
    3 * (distanceSourceRadius r i / 49152) = r / (2 : ℝ) ^ (i + 15) := by
  unfold distanceSourceRadius
  rw [pow_add, pow_add]
  norm_num
  ring

/-- The actual local mass matrix uses the inverse of the original mean
Gram. The exact normalization used in its proof has disappeared from the
quadratic estimate, and the physical mass scaling has been cancelled. -/
theorem regular_pair_mean_pinching {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hhessian : LocalPoissonHessianInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (haction : LocalPoissonHessianActionInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n)
    {A B J Cχ Cg D Ca P : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hCχ : 0 ≤ Cχ) (hP : 0 < P) :
    ∃ Cpin tau : ℝ, 0 < Cpin ∧ 0 < tau ∧
    ∀ {base first center : X} {a C enlargement zeta eta : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
      (e : RegularProjectionEnvironment hX base hk a |K| B J C A Cχ enlargement zeta eta)
      (_hfirst : first ∈ ball base (e.heat.radius / 32))
      (_hcenter : center ∈ ball base (e.heat.radius / 32))
      (d1 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca first)
      (d2 : RegularCenterRadialData hX e.heat |K| B J C A Cχ eta Cg D Ca center),
    0 ≤ zeta → zeta ≤ tau → ∀ i,
    let μ := hausdorff n X
    let s := distanceSourceRadius e.heat.radius i
    let rho := s / 49152
    let _U := (centeredSobolevMap μ hX.quadratic e.heat.coordinates e.one.sobolev
      (e.heat.values center)).comp (d2.frame i).toContinuousLinearMap
    let _delta := (d2.frame i : Euclidean n →L[ℝ] Euclidean n).adjoint
      (e.heat.values first - e.heat.values center)
    let sigma := twoCenterProjectionSource (radialFitQualitativeConstant n Cχ * zeta)
      (normalizedPoissonDefect μ hX.quadratic d1.source)
      (normalizedPoissonDefect μ hX.quadratic d2.source) i
    dist first center ≤ s / 512 → sigma ^ 2 ≤ tau →
    regularPairProjectionSize hX e d1 d2 i ≤ P * sigma →
    ∃ R : Euclidean n ≃L[ℝ] Euclidean n,
      R.toContinuousLinearMap = sobolevMeanGram μ hX.quadratic
        (sobolevColumnMap μ hX.quadratic e.heat.coordinates)
        (ball center (3 * rho)) measurableSet_ball ∧
      R.toContinuousLinearMap.IsPositive ∧
      let D := frozenConjugate R ((s ^ 2 / s ^ n) • e.heat.mass.massOperator (ball center rho))
      D.IsPositive ∧
      ⟪e.heat.values first - e.heat.values center,
        D (e.heat.values first - e.heat.values center)⟫_ℝ ≤ Cpin * s ^ 2 * sigma ^ 2 := by
  obtain ⟨Cpin, tau, hCpin, htau, hpin⟩ := regular_pair_pinching hX hhessian hcutoff
    haction hgradient hmean hn hA hB hJ hCχ hP (Cg := Cg) (D := D) (Ca := Ca)
  refine ⟨Cpin, tau, hCpin, htau, ?_⟩
  intro base first center a C enlargement zeta eta ker hk e hfirst hcenter d1 d2
    hzeta hzt i μ s rho U delta sigma hroom hsigma hsharp
  obtain ⟨N, hN, _hNnorm, hmass⟩ := hpin e hfirst hcenter d1 d2 hzeta hzt i hroom hsigma hsharp
  let A := N.trans (d2.frame i)
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hsub : ball center (3 * rho) ⊆ ball center (2 * s) :=
    ball_subset_ball (by dsimp only [rho]; linarith)
  have hone := ae_restrict_of_ae_restrict_of_subset hsub (e.oneRepresentative center hcenter i)
  have hraw : IsExactMeanNormalization μ hX.quadratic
      (sobolevColumnMap μ hX.quadratic e.heat.coordinates)
      (ball center (3 * rho)) measurableSet_ball A := by
    have hh := uncentered_frame_normalization μ hX.quadratic e.heat.coordinates
      e.one.sobolev (e.heat.values center) (d2.frame i) N
      (ball center (3 * rho)) measurableSet_ball hone hN
    have hcomp : A.toContinuousLinearMap =
        (d2.frame i).toContinuousLinearMap.comp N.toContinuousLinearMap := by
      ext v
      rfl
    change sobolevMeanGram μ hX.quadratic
      ((sobolevColumnMap μ hX.quadratic e.heat.coordinates).comp A.toContinuousLinearMap)
      (ball center (3 * rho)) measurableSet_ball = _
    rw [hcomp]
    exact hh
  let R := meanGramEquiv μ hX.quadratic (sobolevColumnMap μ hX.quadratic e.heat.coordinates)
    (ball center (3 * rho)) measurableSet_ball A hraw
  have hR : R.toContinuousLinearMap = sobolevMeanGram μ hX.quadratic
      (sobolevColumnMap μ hX.quadratic e.heat.coordinates)
      (ball center (3 * rho)) measurableSet_ball := by
    ext v
    rfl
  have hinv : R.symm (e.heat.values first - e.heat.values center) =
      d2.frame i (N (N.toContinuousLinearMap.adjoint delta)) := by
    rw [meanGramEquiv_symm_apply]
    have hcomp : A.toContinuousLinearMap =
        (d2.frame i).toContinuousLinearMap.comp N.toContinuousLinearMap := by
      ext v
      rfl
    rw [hcomp, ContinuousLinearMap.adjoint_comp]
    rfl
  have hscale : 0 ≤ s ^ 2 / s ^ n := by positivity
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · rw [hR]
    exact sobolevMeanGram_isPositive μ hX.quadratic _ _ _
  · exact frozenConjugate_isPositive R
      ((e.heat.mass.massOperator_isPositive _ measurableSet_ball).smul_of_nonneg hscale)
  · rw [inner_frozenConjugate, smul_apply, inner_smul_right, hinv]
    calc
      _ ≤ (s ^ 2 / s ^ n) * (Cpin * s ^ n * sigma ^ 2) :=
        mul_le_mul_of_nonneg_left hmass hscale
      _ = Cpin * s ^ 2 * sigma ^ 2 := by
        field_simp

end RegularPointCoordinates

end

end OAI

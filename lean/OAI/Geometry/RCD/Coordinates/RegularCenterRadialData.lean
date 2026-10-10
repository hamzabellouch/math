import OAI.Geometry.RCD.Coordinates.RegularProjectionEnvironment
import OAI.Geometry.RCD.Coordinates.RadialMatrixEstimates

namespace OAI

/-! # Actual radial data at every center of the common heat neighborhood -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Sources, normalizing frames and radial fits all use the same harmonic map. -/
structure RegularCenterRadialData {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    [(hausdorff n X).Regular]
    {p : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {enlargement zeta : ℝ} (heat : RegularBilinearData hX p hk enlargement zeta)
    (κ B J C A Cχ eta Cg D Ca : ℝ) (q : X) where
  source : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ q heat.radius
  replacement : DyadicDistanceReplacements (hausdorff n X) hX.quadratic source B J C
  summable : Summable (normalizedPoissonDefect (hausdorff n X) hX.quadratic source)
  budget : (∑' i, normalizedPoissonDefect (hausdorff n X) hX.quadratic source i) < eta
  gradient : ∀ i z, dist z q ≤ distanceSourceRadius heat.radius i / 4 →
    ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius heat.radius i / 4)),
      localGamma (hausdorff n X) hX.quadratic (replacement.replacement i)
        (replacement.replacement i) x ≤ (A * distanceSourceRadius heat.radius i) ^ 2
  cutoff : ∀ i, GoodLaplacianCutoff (hausdorff n X) hX.quadratic q
    (distanceSourceRadius heat.radius i / 64) Cχ
  frame : ℕ → Euclidean n ≃L[ℝ] Euclidean n
  exactFrame : ∀ i, IsExactMeanNormalization (hausdorff n X) hX.quadratic
    (sobolevColumnMap (hausdorff n X) hX.quadratic heat.coordinates)
    (ball q (2 * distanceSourceRadius heat.radius i)) measurableSet_ball (frame i)
  splitting : ∀ i, FirstOrderSplittingOn (hausdorff n X) hX.quadratic q
    (2 * distanceSourceRadius heat.radius i) zeta
    (transformedColumn (hausdorff n X) hX.quadratic heat.coordinates (frame i))
    (fun x => (frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (heat.values x))
  metric : ∀ i, IsPointedApproximation q 0 (distanceSourceRadius heat.radius i / 64) 4 zeta
    (fun x => (distanceSourceRadius heat.radius i / 64)⁻¹ •
      ((frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (heat.values x) -
        (frame i : Euclidean n →L[ℝ] Euclidean n).adjoint (heat.values q)))
  rows : RadialMatrixEstimates hX source replacement heat.coordinates heat.values frame cutoff
    zeta Cg D Ca A

/-- Uniform radial constants can be chosen before any neighborhood or error
size. This uses the proved radial estimates and the fixed heat degree. -/
theorem regular_center_radial_constants {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    (hhessian : LocalPoissonHessianInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    {B J A Cχ : ℝ} {degree : ℕ} (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A)
    (hCχ : 0 ≤ Cχ) (hdegree : 0 < degree) :
    ∃ Cg D Ca : ℝ, 1 ≤ Cg ∧ 0 < D ∧ 1 ≤ Ca ∧
    ∀ {p : X} {a κ C enlargement zeta eta : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker},
      0 ≤ a → 0 ≤ κ → -κ ≤ K → 0 ≤ zeta →
      radialNormalizationRestrictionConstant (m + 2) * zeta ≤ 1 →
      ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * zeta) ≤ 1 / 64 →
      BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a) →
      ∀ e : RegularProjectionEnvironment hX p hk a κ B J C A Cχ enlargement zeta eta,
      e.heat.degree = degree → ∀ q ∈ ball p (e.heat.radius / 32),
      Nonempty (RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca q) := by
  classical
  obtain ⟨Cg, D, Ca, hCg, hD, hCa, hrows⟩ := dyadic_radial_matrices_uniform m hX hhessian
    hmean hgradient hB hJ hA hCχ (show (0 : ℝ) ≤ 1 by norm_num) hdegree
  refine ⟨Cg, D, Ca, hCg, hD, hCa, ?_⟩
  intro p a κ C enlargement zeta eta ker hk ha hκ hK hzeta hsmall1 hsmall hBG e hdeg q hq
  let R := e.heat.radius
  let u := e.heat.coordinates
  let V := e.heat.values
  let μ := hausdorff (m + 2) X
  have hR : 0 < R := e.heat.radius_pos
  have hs (i : ℕ) : 0 < distanceSourceRadius R i := distanceSourceRadius_pos hR i
  have hsR (i : ℕ) : distanceSourceRadius R i ≤ R := by
    have hh := distanceSourceRadius_outer_le hR.le i
    linarith [hs i]
  have hsub : ball q R ⊆ ball p (32 * R) := by
    intro x hx
    have hxp := dist_triangle x q p
    have hxq := mem_ball.mp hx
    have hqp := mem_ball.mp hq
    change dist x p < 32 * R
    change dist q p < R / 32 at hqp
    linarith
  let gramSize (j k : Fin (m + 2)) := (μ.real (ball q R))⁻¹ * ∫ x in ball q R,
    |localGamma μ hX.quadratic (u j) (u k) x - (if j = k then 1 else 0)| ∂μ
  let gramBudget := ∑ j : Fin (m + 2), ∑ k : Fin (m + 2), |gramSize j k|
  have hgramBudget : 0 ≤ gramBudget := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hgram (j k : Fin (m + 2)) : gramSize j k ≤ gramBudget := by
    have hrow : |gramSize j k| ≤ ∑ l : Fin (m + 2), |gramSize j l| :=
      Finset.single_le_sum (f := fun l : Fin (m + 2) => |gramSize j l|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have hsum : (∑ l : Fin (m + 2), |gramSize j l|) ≤ gramBudget :=
      Finset.single_le_sum (f := fun j : Fin (m + 2) => ∑ l : Fin (m + 2), |gramSize j l|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
        (Finset.mem_univ j)
    exact (le_abs_self _).trans (hrow.trans hsum)
  have huq : FirstOrderSplittingOn μ hX.quadratic q R
      (e.heat.initialError + gramBudget) u V := by
    refine {
      representative := fun j => ae_restrict_of_ae_restrict_of_subset hsub
        (e.heat.splitting.representative j)
      continuous := e.heat.splitting.continuous.mono hsub
      harmonic := fun j => (e.heat.splitting.harmonic j).mono μ hX.quadratic hsub
      gradient := ?_
      gram := ?_ }
    · intro j
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (e.heat.splitting.gradient j)]
        with x hx
      apply hx.trans
      have he := e.heat.initialError_pos
      nlinarith
    · intro j k
      exact (hgram j k).trans (le_add_of_nonneg_left e.heat.initialError_pos.le)
  obtain ⟨S, T, hP, hbudget, hgrad, hcut⟩ := e.poisson q hq
  let χ := fun i => Classical.choice (hcut i)
  obtain ⟨_, _, hfit, F, hexact, hfirst, hmetric⟩ := e.heat.localData q hq
  let w := fun i x => (F i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (V x)
  have hrad (i : ℕ) : 2 * distanceSourceRadius R i = R / (2 : ℝ) ^ i := by
    unfold distanceSourceRadius
    rw [pow_succ]
    ring
  have htest (i : ℕ) : distanceSourceRadius R i / 64 = (R / (2 : ℝ) ^ i) / 128 := by
    have hh := hrad i
    linarith
  dsimp only [R] at hrad htest
  have hbase (i : ℕ) (j : Fin (m + 2)) : ∀ᵐ x ∂μ.restrict (ball q (distanceSourceRadius R i / 64)),
      localGamma μ hX.quadratic (u j) (u j) x ≤ (2 : ℝ) ^ 2 := by
    have hsub' : ball q (distanceSourceRadius R i / 64) ⊆ ball p (32 * R) :=
      (ball_subset_ball (by linarith [hs i, hsR i])).trans hsub
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub' (e.heat.splitting.gradient j)] with x hx
    exact hx.trans (by nlinarith [e.heat.initialError_pos, e.heat.initialError_le_one])
  have hcurv (i : ℕ) : -(1 : ℝ) ≤ K * (distanceSourceRadius R i / 64) ^ 2 := by
    have hsquare : (distanceSourceRadius R i / 64) ^ 2 ≤ R ^ 2 := by nlinarith [hs i, hsR i]
    have habs := mul_le_mul_of_nonneg_left hsquare (abs_nonneg K)
    have hlo := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (distanceSourceRadius R i / 64))
    have he := e.curvature
    have hkR := mul_nonneg hκ (sq_nonneg R)
    change 4 * (|K| + κ) * R ^ 2 ≤ 1 at he
    nlinarith
  have hresult := hrows ha hκ hK e.heat.radius_le_one e.modelScale hBG S T hP
    (fun t ht htR => e.volume q hq t ht (by linarith)) u hbase F w hzeta hsmall1 hsmall
    (fun i => by simpa only [R, u, V, w, hrad] using hexact i)
    (fun i => by simpa only [R, u, V, w, hrad] using hfirst i)
    (fun i => by simpa only [R, u, V, w, htest] using hmetric i)
    (fun i => hgrad i q (by have hsi := hs i; simp only [dist_self]; change 0 ≤ distanceSourceRadius R i / 4; linarith)) χ
    (fun i => by
      have hsi := hs i
      rw [← hdeg]
      exact hfit _ (by positivity) (by linarith [hs i, hsR i])) V huq hcurv
  exact ⟨{
    source := S
    replacement := T
    summable := hP
    budget := hbudget
    gradient := hgrad
    cutoff := χ
    frame := F
    exactFrame := fun i => by simpa only [R, u, V, w, hrad] using hexact i
    splitting := fun i => by simpa only [R, u, V, w, hrad] using hfirst i
    metric := fun i => by simpa only [R, u, V, w, htest] using hmetric i
    rows := hresult }⟩

end RegularPointCoordinates

end

end OAI

import OAI.Geometry.RCD.Sobolev.ActualPoissonMass
import OAI.Geometry.RCD.Sobolev.PoissonPairSpan
import OAI.Geometry.RCD.Coordinates.PoissonSpanCoordinates
import OAI.Geometry.RCD.Harmonic.RadialHarmonicApproximation

namespace OAI

/-! # Harmonic correction of the actual distance radial derivatives -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The full Poisson mass calculation and localized Hessian input now
construct a harmonic approximation to each actual coordinate radial
derivative, with a squared error linear in the same source mass. -/
theorem actual_distance_radial_approximation {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hn : 2 ≤ n) (hhessian : LocalPoissonHessianInput hX)
    {κ r0 B J C A epsilon Cχ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon) (hCχ : 0 ≤ Cχ)
    (p : X) (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0)
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C) (i : ℕ)
    (hs1 : distanceSourceRadius r0 i ≤ 1)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball p (distanceSourceRadius r0 i / 4)) (u j))
    (hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + epsilon) ^ 2)
    (hf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    (hvol : 0 < (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)))
    (hdouble : 2 * (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)) ≤
      (hausdorff n X).real (ball p (2 * (distanceSourceRadius r0 i / 64)))) :
    let s := distanceSourceRadius r0 i
    let q := positiveSquaredDistance (hausdorff n X) hX.quadratic
      (by have := distanceSourceRadius_pos S.radius_pos i; positivity : 0 ≤ 4 * s) (T.cutoff i)
    let P := annularPoincareConstant K n * (s / 64) ^ 2
    ∃ L : ℝ≥0, (L : ℝ) = ((n + 2 : ℕ) : ℝ) * max (1 + epsilon) (A * s) ∧
      ∀ j : Fin n, ∃ h : SobolevSpace (hausdorff n X) hX.quadratic,
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (s / 64)) h ∧
        (∫ x in ball p (s / 64),
          (localGamma (hausdorff n X) hX.quadratic q (u j) x -
            SobolevSpace.toLp (hausdorff n X) hX.quadratic h x) ^ 2 ∂hausdorff n X) ≤
          2 * (1 + epsilon) ^ 2 * ((S.source i).real (ball p s) * (B * s ^ 2)) +
            8 * P * (L : ℝ) ^ 2 *
              (4096 * Cχ * (J + B / 2) * (S.source i).real (ball p s) +
                κ * A ^ 2 * s ^ 2 * (hausdorff n X).real (ball p s)) := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius r0 i
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  let q := positiveSquaredDistance μ hQ (by positivity : 0 ≤ 4 * s) (T.cutoff i)
  let P := annularPoincareConstant K n * (s / 64) ^ 2
  have hP : 0 ≤ P := mul_nonneg (annularPoincareConstant_pos K n).le (sq_nonneg _)
  have hpoin := hX.annular_dirichlet_poincare hn p (by positivity : 0 < s / 64)
    (by change s ≤ 1 at hs1; linarith : s / 64 ≤ 1) hvol hdouble
  obtain ⟨L, hL, M, henergy, hshift, hpair⟩ := actual_poisson_pair_span hX hhessian
    hκ hK hA hepsilon p p p S S T T i
    (by rw [dist_self]; positivity) (by rw [dist_self]; positivity) u hu hgrad hf hf
  let f : Fin 2 → SobolevSpace μ hQ := ![T.replacement i, T.replacement i]
  let U := sobolevColumnMap μ hQ (poissonSpan μ hQ u f)
  let ell := poissonSpanLaplacian n ((n : ℝ) + κ * (4 * s) ^ 2)
  let v : Euclidean (n + 2) := EuclideanSpace.single (Fin.natAdd n (0 : Fin 2)) 1
  have hv : U v = T.replacement i := poissonSpanMap_right μ hQ u f 0
  have hell : ell v = (n : ℝ) + κ * (4 * s) ^ 2 := poissonSpanLaplacian_right _ 0
  let _ : IsFiniteMeasure (μ.restrict (ball p (2 * (s / 32)))) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  obtain ⟨Genergy⟩ := henergy v
  have hfsmall : ∀ᵐ x ∂μ.restrict (ball p (2 * (s / 32))),
      localGamma μ hQ (T.replacement i) (T.replacement i) x ≤ A ^ 2 * s ^ 2 := by
    have ht := ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : 2 * (s / 32) ≤ s / 4)) hf
    simpa only [mul_pow] using ht
  have hmass := T.shifted_mass_le μ hQ i hκ hCχ
    (by rw [dist_self]; positivity) ell Genergy hv hell hshift χ hfsmall
  let F := 4096 * Cχ * (J + B / 2) * (S.source i).real (ball p s) +
    κ * A ^ 2 * s ^ 2 * μ.real (ball p s)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨L, hL, ?_⟩
  intro j
  let w : Euclidean (n + 2) := EuclideanSpace.single (Fin.castAdd 2 j) 1
  have hw : U w = u j := poissonSpanMap_left μ hQ u f j
  have hwnorm : ‖w‖ = 1 := by simp [w, PiLp.norm_single]
  obtain ⟨G, hG⟩ := hpair v w (s / 64) (by positivity) (by linarith)
  change LocalHessianPairing μ hQ (ball p (s / 64)) (U v) (U w) at G
  change ∀ b : ℝ, ∀ φ : SobolevSpace.dirichlet μ hQ (ball p (s / 64)),
    (G.hessian φ - b * energyForm μ hQ (U w) φ.val) ^ 2 ≤
      ((L : ℝ) ^ 2 * ‖w‖ ^ 2 * ((M.measure v).real (ball p (s / 64)) -
        (2 * b * ell v - (n : ℝ) * b ^ 2) * μ.real (ball p (s / 64)))) *
      energyForm μ hQ φ.val φ.val at hG
  have hmass' : (M.measure v).real (ball p (s / 64)) -
      (2 * ell v - (n : ℝ)) * μ.real (ball p (s / 64)) ≤ F := by
    have hm := ShiftedBochnerMeasure.mass M (μ.restrict (ball p (2 * (s / 32))))
      ell (n : ℝ) hshift v 1 (ball p (s / 64)) measurableSet_ball
    rw [measureReal_restrict_apply measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball (by linarith : s / 64 ≤ 2 * (s / 32)))] at hm
    simp only [one_pow, mul_one] at hm
    change ((shiftedBochnerMeasure M (μ.restrict (ball p (2 * (s / 32))))
      ell (n : ℝ) hshift).measure (WithLp.toLp 2 (v, (1 : ℝ)))).real
        (ball p (s / 64)) ≤ F at hmass
    rwa [hm] at hmass
  have hhessian' (φ : SobolevSpace.dirichlet μ hQ (ball p (s / 64))) :
      (G.hessian φ - 1 * energyForm μ hQ (U w) φ.val) ^ 2 ≤
        ((L : ℝ) ^ 2 * F) * energyForm μ hQ φ.val φ.val := by
    have ht := hG 1 φ
    simp only [one_pow, mul_one, one_mul, hwnorm] at ht
    simpa only [one_mul] using ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass' (sq_nonneg (L : ℝ)))
      (by rw [energyForm_self]; exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hQ _)))
  have ha := (hu j).mono μ hQ (ball_subset_ball (by linarith : s / 64 ≤ s / 4))
  have hcoord := ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith : s / 64 ≤ s / 4)) (hgrad j)
  have hlap := T.laplacian_on_ball μ hQ i p
    (by rw [dist_self]; linarith : s / 64 + dist p p ≤ s)
  have herr := T.local_energy_error μ hQ i (ball p (s / 64))
  obtain ⟨h, _, hh, _, he⟩ := G.radial_harmonic_approximation μ hQ measurableSet_ball q
    (by simpa only [hv] using hlap) (by simpa only [hw] using ha)
    1 hP (mul_nonneg (sq_nonneg (L : ℝ)) hF) (sq_nonneg (1 + epsilon))
    (by simpa only [hw] using hcoord) hpoin (by simpa only [hv] using herr) hhessian'
  rw [hw] at he
  refine ⟨h, hh, he.trans_eq ?_⟩
  dsimp only [P, F]
  ring

end RegularPointCoordinates

end

end OAI

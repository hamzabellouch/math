import OAI.Geometry.RCD.Sobolev.ActualPoissonMass
import OAI.Geometry.RCD.Sobolev.PoissonPairSpan
import OAI.Geometry.RCD.Sobolev.PoissonSpanLift

namespace OAI

/-! # The genuine Poisson radial derivative in every coordinate covector -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The common published Hessian span supplies the actual radial Sobolev
function in every covector, with the full shifted mass budget. -/
theorem actual_distance_radial_pairing {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianInput hX)
    {κ r0 B J C A ε Cχ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hCχ : 0 ≤ Cχ)
    (p : X) (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0)
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C) (i : ℕ)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball p (distanceSourceRadius r0 i / 4)) (u j))
    (hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + ε) ^ 2)
    (hf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ) :
    let μ := hausdorff n X
    let s := distanceSourceRadius r0 i
    ∃ L : ℝ≥0, (L : ℝ) = ((n + 2 : ℕ) : ℝ) * max (1 + ε) (A * s) ∧
      ∀ b : Euclidean n,
      ∃ G : LocalHessianPairing μ hX.quadratic (ball p (s / 64)) (T.replacement i)
        (sobolevColumnMap μ hX.quadratic u b),
      ∀ φ : SobolevSpace.dirichlet μ hX.quadratic (ball p (s / 64)),
        (G.hessian φ - energyForm μ hX.quadratic (sobolevColumnMap μ hX.quadratic u b) φ.val) ^ 2 ≤
          ((L : ℝ) ^ 2 * ‖b‖ ^ 2 *
            (4096 * Cχ * (J + B / 2) * (S.source i).real (ball p s) +
              κ * A ^ 2 * s ^ 2 * μ.real (ball p s))) * energyForm μ hX.quadratic φ.val φ.val := by
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius r0 i
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  obtain ⟨L, hL, M, henergy, hshift, hpair⟩ := actual_poisson_pair_span hX hhessian
    hκ hK hA hε p p p S S T T i
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
  let D := 4096 * Cχ * (J + B / 2) * (S.source i).real (ball p s) +
    κ * A ^ 2 * s ^ 2 * μ.real (ball p s)
  have hmass' : (M.measure v).real (ball p (s / 64)) -
      (2 * ell v - (n : ℝ)) * μ.real (ball p (s / 64)) ≤ D := by
    have hm := ShiftedBochnerMeasure.mass M (μ.restrict (ball p (2 * (s / 32))))
      ell (n : ℝ) hshift v 1 (ball p (s / 64)) measurableSet_ball
    rw [measureReal_restrict_apply measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball (by linarith : s / 64 ≤ 2 * (s / 32)))] at hm
    simp only [one_pow, mul_one] at hm
    change ((shiftedBochnerMeasure M (μ.restrict (ball p (2 * (s / 32))))
      ell (n : ℝ) hshift).measure (WithLp.toLp 2 (v, (1 : ℝ)))).real (ball p (s / 64)) ≤ D at hmass
    rwa [hm] at hmass
  refine ⟨L, hL, ?_⟩
  intro b
  let w := poissonCoordinateLift b
  have hw : U w = sobolevColumnMap μ hQ u b := poissonSpanMap_lift μ hQ u f b
  have hwnorm : ‖w‖ = ‖b‖ := poissonCoordinateLift_norm b
  obtain ⟨G, hG⟩ := hpair v w (s / 64) (by positivity) (by linarith)
  have hresult : ∃ H : LocalHessianPairing μ hQ (ball p (s / 64)) (U v) (U w),
      ∀ φ : SobolevSpace.dirichlet μ hQ (ball p (s / 64)),
      (H.hessian φ - energyForm μ hQ (U w) φ.val) ^ 2 ≤
        ((L : ℝ) ^ 2 * ‖b‖ ^ 2 * D) * energyForm μ hQ φ.val φ.val := by
    refine ⟨G, ?_⟩
    intro φ
    have ht := hG 1 φ
    simp only [one_pow, mul_one, one_mul, hwnorm] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass' (mul_nonneg (sq_nonneg (L : ℝ)) (sq_nonneg ‖b‖)))
      (by rw [energyForm_self]; exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hQ _)))
  rw [hv, hw] at hresult
  exact hresult

end RegularPointCoordinates

end

end OAI

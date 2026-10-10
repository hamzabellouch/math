import OAI.Geometry.RCD.Metric.SquaredDistanceInequality
import OAI.Geometry.RCD.Metric.SquaredDistanceLocality
import OAI.Geometry.RCD.Sobolev.CompactLipschitzTests

namespace OAI

/-! # Finite-mass bound for the squared-distance distribution

A cutoff in the ball of triple radius majorizes every nonnegative test in
the original ball. Positivity on the larger ball gives a uniform mass bound.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.squaredDistance_functional_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (p : X) {R : ℝ} (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f : compactLipschitzTests (ball p R),
      compactTestEnergy (hausdorff n X) hX.quadratic (ball p R)
        (inwardQuadratic (hausdorff n X) hX.quadratic p hR.le) ((n : ℝ) + κ * R ^ 2) f ≤
          M * ‖(f : X →ᵇ ℝ) ⊔ 0‖ := by
  let μ := hausdorff n X
  let q := inwardQuadratic μ hX.quadratic p hR.le
  let Q := inwardQuadratic μ hX.quadratic p (by linarith : 0 ≤ 3 * R)
  let a := (n : ℝ) + κ * R ^ 2
  let A := (n : ℝ) + κ * (3 * R) ^ 2
  let χ := radialCutoff p R
  have hχ := radialCutoff_lipschitz p hR
  have hcχ := radialCutoff_hasCompactSupport p hR
  have hsχ : tsupport χ ⊆ ball p (3 * R) := by
    have hs : tsupport χ ⊆ closedBall p (2 * R) := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      by_contra hn'
      exact hx (radialCutoff_eq_zero p hR (by
        exact (not_le.mp (by simpa only [mem_closedBall, dist_comm] using hn')).le))
    exact hs.trans (closedBall_subset_ball (by linarith))
  let u := SobolevSpace.ofLipschitzCompact μ hX.quadratic hχ hcχ
  have hu : SobolevSpace.toLp μ hX.quadratic u =ᵐ[μ] χ :=
    SobolevSpace.ofLipschitzCompact_coe μ hX.quadratic hχ hcχ
  let M := energyForm μ hX.quadratic Q u + A * ∫ x, χ x ∂μ
  have hM : 0 ≤ M := hX.squaredDistance_laplacian_test hn hκ hK p
    (by linarith : 0 < 3 * R) u χ hχ hcχ hsχ hu (fun x => (radialCutoff_bounds p R x).1)
  let F := compactTestEnergy μ hX.quadratic (ball p R) q a
  have hpos (f : compactLipschitzTests (ball p R)) (hf : 0 ≤ (f : X →ᵇ ℝ)) : 0 ≤ F f :=
    hX.squaredDistance_laplacian_test hn hκ hK p hR _ _ f.property.choose_spec.1
      f.property.choose_spec.2.1 f.property.choose_spec.2.2
      (compactTestSobolev_coe μ hX.quadratic _ f) hf
  have hbound (f : compactLipschitzTests (ball p R)) (hf : 0 ≤ (f : X →ᵇ ℝ)) :
      F f ≤ M * ‖(f : X →ᵇ ℝ)‖ := by
    let g := compactTestSobolev μ hX.quadratic (ball p R) f
    let C := ‖(f : X →ᵇ ℝ)‖
    have hC : 0 ≤ C := norm_nonneg _
    let v := fun x => C * χ x - (f : X →ᵇ ℝ) x
    have hv := ((lipschitzWith_smul C).comp hχ).sub f.property.choose_spec.1
    have hcv : HasCompactSupport v := (hcχ.smul_left (f := fun _ => C)).sub f.property.choose_spec.2.1
    have hsv : tsupport v ⊆ ball p (3 * R) :=
      (tsupport_sub _ _).trans (union_subset
        ((tsupport_smul_subset_right (fun _ => C) χ).trans hsχ)
        (f.property.choose_spec.2.2.trans (ball_subset_ball (by linarith))))
    have hv0 (x : X) : 0 ≤ v x := by
      by_cases hx : (f : X →ᵇ ℝ) x = 0
      · dsimp only [v]
        rw [hx, sub_zero]
        exact mul_nonneg hC (radialCutoff_bounds p R x).1
      · have hxb : x ∈ ball p R := f.property.choose_spec.2.2 (subset_tsupport _ hx)
        have hχx : χ x = 1 := radialCutoff_eq_one p hR (by
          simpa only [mem_ball, dist_comm] using (mem_ball.mp hxb).le)
        dsimp only [v]
        rw [hχx, mul_one]
        exact sub_nonneg.mpr ((f : X →ᵇ ℝ).apply_le_norm x)
    have hrep : SobolevSpace.toLp μ hX.quadratic (C • u - g) =ᵐ[μ] v := by
      filter_upwards [Lp.coeFn_sub (C • SobolevSpace.toLp μ hX.quadratic u)
        (SobolevSpace.toLp μ hX.quadratic g), Lp.coeFn_smul C (SobolevSpace.toLp μ hX.quadratic u),
        hu, compactTestSobolev_coe μ hX.quadratic _ f] with x hs hm hu' hf'
      change (C • SobolevSpace.toLp μ hX.quadratic u - SobolevSpace.toLp μ hX.quadratic g) x = _
      change SobolevSpace.toLp μ hX.quadratic g x = (f : X →ᵇ ℝ) x at hf'
      simp only [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hu', hf', v]
    have hh := hX.squaredDistance_laplacian_test hn hκ hK p
      (by linarith : 0 < 3 * R) (C • u - g) v hv hcv hsv hrep hv0
    have hfi : Integrable (f : X →ᵇ ℝ) μ :=
      (f : X →ᵇ ℝ).continuous.integrable_of_hasCompactSupport f.property.choose_spec.2.1
    have hχi : Integrable χ μ := hχ.continuous.integrable_of_hasCompactSupport hcχ
    have hrad := inwardQuadratic_energy_radius μ hX.quadratic p hR.le
      (by linarith : R ≤ 3 * R) g (f : X →ᵇ ℝ) f.property.choose_spec.1
      f.property.choose_spec.2.1 f.property.choose_spec.2.2
      (compactTestSobolev_coe μ hX.quadratic _ f)
    change 0 ≤ energyForm μ hX.quadratic Q (C • u - g) + A * ∫ x, v x ∂μ at hh
    rw [energyForm_sub_right, energyForm_smul_right, hrad] at hh
    have hint : (∫ x, v x ∂μ) = C * ∫ x, χ x ∂μ - ∫ x, (f : X →ᵇ ℝ) x ∂μ := by
      exact (integral_sub (hχi.const_mul C) hfi).trans (by rw [integral_const_mul])
    rw [hint] at hh
    have hi : 0 ≤ ∫ x, (f : X →ᵇ ℝ) x ∂μ := integral_nonneg hf
    have haA : a ≤ A := by dsimp only [a, A]; nlinarith [mul_nonneg hκ (sq_nonneg R)]
    change energyForm μ hX.quadratic q g + a * ∫ x, (f : X →ᵇ ℝ) x ∂μ ≤ M * C
    dsimp only [M]
    nlinarith [mul_le_mul_of_nonneg_right haA hi]
  refine ⟨M, hM, fun f => ?_⟩
  let fpos : compactLipschitzTests (ball p R) :=
    ⟨(f : X →ᵇ ℝ) ⊔ 0, compactLipschitzTests_sup_zero f⟩
  have hm : F f ≤ F fpos := by
    have hh := hpos (fpos - f) (sub_nonneg.mpr (le_sup_left : (f : X →ᵇ ℝ) ≤ (f : X →ᵇ ℝ) ⊔ 0))
    have hadd := F.map_add (fpos - f) f
    have heq : fpos - f + f = fpos := by
      apply Subtype.ext
      ext x
      change (fpos : X →ᵇ ℝ) x - (f : X →ᵇ ℝ) x + (f : X →ᵇ ℝ) x = (fpos : X →ᵇ ℝ) x
      ring
    rw [heq] at hadd
    linarith
  exact hm.trans (hbound fpos le_sup_right)

end RegularPointCoordinates

end

end OAI

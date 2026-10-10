import OAI.Geometry.RCD.Sobolev.HarmonicEnergyIdentification
import OAI.Geometry.RCD.Sobolev.ContinuousDensityTestRigidity
import OAI.Geometry.RCD.Sobolev.EuclideanLocalEnergyRigidity

namespace OAI

/-! # An actual constant-energy harmonic limit is affine on the inner ball -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_constant_energy_gradient_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*r k^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {M : ℝ} (hM : 0 < M) (hnorm : ∀ k, harmonicTargetNorm hX (p k) (5*r k) (w k) ≤ M)
    (g : Euclidean n → ℝ) (hg : ContDiffOn ℝ ∞ g (ball 0 5))
    (hgL : ∀ W < 5, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0 < W → W < 5 → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (V k x)| ≤ δ)
    {C : ℝ}
    (herror : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (5*r k)))⁻¹*
      ∫ x in ball (p k) (4*r k),
        |r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x-C|
        ∂hausdorff n X) atTop (𝓝 0))
    : ∀ x ∈ ball (0 : Euclidean n) 3, ‖fderiv ℝ g x‖^2 = C := by
  have hsub : ball (0 : Euclidean n) 3 ⊆ ball 0 5 := ball_subset_ball (by norm_num)
  have hd : ContinuousOn (fun z => ‖fderiv ℝ g z‖^2) (ball (0 : Euclidean n) 3) :=
    ((hg.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).norm.pow 2).mono hsub
  have hz : EqOn (fun z => ‖fderiv ℝ g z‖^2-C) 0 (ball (0 : Euclidean n) 3) := by
    apply continuous_zero_of_nonnegative_tests isOpen_ball (hd.sub continuousOn_const)
    intro φ hφ hφc hs
    have ht := hX.harmonic_constant_energy_test hn p r ε V hr hcurv hε hε1 hεlim
      hV w hw hM hnorm g hg hgL hconv herror φ hφ hs
    have hprod : Integrable (fun z => φ z*‖fderiv ℝ g z‖^2) volume :=
      (continuous_mul_of_tsupport_subset isOpen_ball hd φ.continuous hs).integrable_of_hasCompactSupport
        hφc.mul_right
    have hconst : Integrable (fun z => φ z*C) volume :=
      (φ.continuous.mul continuous_const).integrable_of_hasCompactSupport hφc.mul_right
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Euclidean n) 5)
      (fun z hz => by
        have hzero : φ z=0 := by
          by_contra hne
          exact hz (hsub (hs (subset_tsupport φ hne)))
        rw [hzero,zero_mul])]
    change (∫ z in ball (0 : Euclidean n) 5, φ z*(‖fderiv ℝ g z‖^2-C)) = 0
    simp_rw [mul_sub]
    rw [integral_sub hprod.integrableOn hconst.integrableOn,integral_mul_const]
    nlinarith [ht]
  have he : ∀ z ∈ ball (0 : Euclidean n) 3, ‖fderiv ℝ g z‖^2=C := by
    intro z hz'
    exact sub_eq_zero.mp (hz hz')
  exact he

theorem NoncollapsedRCD.harmonic_constant_energy_affine_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*r k^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {M : ℝ} (hM : 0 < M) (hnorm : ∀ k, harmonicTargetNorm hX (p k) (5*r k) (w k) ≤ M)
    (g : Euclidean n → ℝ) (hg : ContDiffOn ℝ ∞ g (ball 0 5))
    (hgL : ∀ W < 5, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0 < W → W < 5 → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (V k x)| ≤ δ)
    {C : ℝ}
    (herror : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (5*r k)))⁻¹*
      ∫ x in ball (p k) (4*r k),
        |r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x-C|
        ∂hausdorff n X) atTop (𝓝 0))
    (hh : InnerProductSpace.HarmonicOnNhd g (ball 0 5)) :
    ∀ x ∈ ball (0 : Euclidean n) 3, g x = g 0 + fderiv ℝ g 0 x := by
  have he := hX.harmonic_constant_energy_gradient_limit hn p r ε V hr hcurv hε hε1 hεlim
    hV w hw hM hnorm g hg hgL hconv herror
  have hs : ball (0 : Euclidean n) 3 ⊆ ball 0 5 := ball_subset_ball (by norm_num)
  exact local_harmonic_constant_energy_affine (by norm_num) (hg.mono hs) (hh.mono hs) he

end RegularPointCoordinates

end

end OAI

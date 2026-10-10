import OAI.Geometry.RCD.Harmonic.BoundedHarmonicStrongRecovery
import OAI.Geometry.RCD.Sobolev.BoundedHarmonicScaledEnergy
import OAI.Geometry.RCD.Sobolev.CutoffEnergyCoreConvergence
import OAI.Geometry.RCD.Sobolev.LocalScaledGammaL1
import OAI.Geometry.RCD.Sobolev.WeightedEnergyDifference
import OAI.Geometry.RCD.Sobolev.PointedTestLocalization

namespace OAI

/-! # Compact test energy limits for the original harmonic functions -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_weighted_energy_limit {K : ℝ} {n : ℕ}
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
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0 ≤ φ z) (hs : tsupport φ ⊆ ball 0 3) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (5*r k)))⁻¹*
      ∫ x in ball (p k) (5*r k), φ (V k x)*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x
        ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0 : Euclidean n) 5))⁻¹*
        ∫ z in ball 0 5, φ z*‖fderiv ℝ g z‖^2)) := by
  obtain ⟨F,hF,_,hDF,N,q,_,_,⟨Q,hQ,hQbound⟩,hqe,hstrong⟩ :=
    hX.bounded_harmonic_strong_recovery hn (a:=4) (b:=9/2) (R:=19/4) (T:=39/8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hM p r ε V hr hcurv hε hε1 hεlim hV w hw hnorm g hg hgL hconv
  let μ := hausdorff n X
  let Ω := fun k => ball (p (k+N)) (4*r (k+N))
  let c := fun k => (μ.real (ball (p (k+N)) (5*r (k+N))))⁻¹
  have hmass (k : ℕ) : 0 < μ.real (ball (p (k+N)) (5*r (k+N))) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos (by norm_num) (hr (k+N)))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hc (k : ℕ) : 0 ≤ c k := inv_nonneg.mpr (hmass k).le
  have hcm (k : ℕ) : c k*μ.real (Ω k) ≤ 1 := by
    have hh : μ.real (Ω k) ≤ μ.real (ball (p (k+N)) (5*r (k+N))) :=
      ENNReal.toReal_mono (hX.finiteOnBounded _ isBounded_ball).ne
        (measure_mono (ball_subset_ball (by linarith [hr (k+N)])))
    exact (mul_le_mul_of_nonneg_left hh (hc k)).trans_eq (inv_mul_cancel₀ (hmass k).ne')
  have hcore := cutoff_energy_core_convergence μ hX.quadratic (by norm_num : (4:ℝ)<9/2)
    (by norm_num : (9/2:ℝ)<19/4) (fun k => p (k+N)) (fun k => r (k+N))
    (fun k => r (k+N)^2*c k) (fun k => hr (k+N)) (fun k => mul_nonneg (sq_nonneg _) (hc k))
    (fun k => w (k+N)-(q k).val) hstrong
  obtain ⟨B,hB,hWbound⟩ := hX.bounded_harmonic_scaled_energy_bound hn (S:=5) (R:=4)
    (by norm_num) (by norm_num) (by norm_num) hM p r hr hcurv w hw hnorm
  have hclose := local_scaled_gamma_l1_tendsto μ hX.quadratic Ω
    (fun k => (hX.finiteOnBounded _ isBounded_ball).ne) (fun k => r (k+N)) c
    (fun k => hr (k+N)) hc hcm (Real.sqrt_nonneg B) hQ
    (fun k => w (k+N)) (fun k => (q k).val)
    (Eventually.of_forall (fun k => by
      simpa only [Real.sq_sqrt hB] using
        ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall (hWbound (k+N))))
    (hQbound.mono (fun _ h => ae_restrict_of_ae h))
    (by convert hcore using 1; funext k; ring)
  let e := fun k x => r (k+N)^2*localGamma μ hX.quadratic (w (k+N)) (w (k+N)) x
  let e' := fun k x => r (k+N)^2*localGamma μ hX.quadratic (q k).val (q k).val x
  let θ := fun k x => φ (V (k+N) x)
  have hdiff := weighted_integral_difference_tendsto μ Ω c hc e e' θ
    (fun k => ((localGamma_memL1 μ hX.quadratic (w (k+N)) (w (k+N))).const_mul _).integrableOn)
    (fun k => ((localGamma_memL1 μ hX.quadratic (q k).val (q k).val).const_mul _).integrableOn)
    (fun k => (φ.continuous.measurable.comp (hV (k+N)).measurable).aestronglyMeasurable.restrict)
    (fun k => Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using φ.norm_coe_le_norm (V (k+N) x)))
    (by simpa only [e,e',mul_sub] using hclose)
  have hloc : ∀ᶠ k in atTop, ∀ f : X → ℝ,
      (∫ x in Ω k, θ k x*f x ∂μ) =
        ∫ x in ball (p (k+N)) (5*r (k+N)), θ k x*f x ∂μ := by
    filter_upwards [(hεlim.comp (tendsto_add_atTop_nat N)).eventually
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))] with k hk
    intro f
    apply pointed_test_integral_localization μ (hr (k+N)) (by norm_num : (0:ℝ)≤5)
      (by dsimp only [Function.comp_def] at hk; linarith : (3:ℝ)+2*ε (k+N)≤4)
      (by norm_num : (4:ℝ)≤5) (hV (k+N)).metric φ ((subset_tsupport φ).trans hs) f measurableSet_ball
  have hdiff' : Tendsto (fun k => c k*(∫ x in ball (p (k+N)) (5*r (k+N)), θ k x*e k x ∂μ)-
      c k*(∫ x in ball (p (k+N)) (5*r (k+N)), θ k x*e' k x ∂μ)) atTop (𝓝 0) :=
    hdiff.congr' (hloc.mono (fun k hk => by rw [hk (e k),hk (e' k)]))
  have hφS : tsupport φ ⊆ ball (0 : Euclidean n) 5 :=
    hs.trans (ball_subset_ball (by norm_num))
  have hqenergy := hqe φ hφ hφS
  have hDFint : (∫ z in ball (0 : Euclidean n) 5, φ z*‖fderiv ℝ F z‖^2) =
      ∫ z in ball (0 : Euclidean n) 5, φ z*‖fderiv ℝ g z‖^2 := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z _
    dsimp only
    by_cases hz : φ z=0
    · simp only [hz,zero_mul]
    · rw [hDF ((ball_subset_ball (by norm_num : (3:ℝ)≤39/8)) (hs (subset_tsupport φ hz)))]
  rw [hDFint] at hqenergy
  have heq (k : ℕ) (u : SobolevSpace μ hX.quadratic) :
      c k*(∫ x in ball (p (k+N)) (5*r (k+N)), θ k x*(r (k+N)^2*localGamma μ hX.quadratic u u x) ∂μ) =
      r (k+N)^2*c k*(∫ x in ball (p (k+N)) (5*r (k+N)), θ k x*localGamma μ hX.quadratic u u x ∂μ) := by
    simp_rw [mul_left_comm (θ k _) (r (k+N)^2)]
    rw [integral_const_mul]
    ring
  simp only [e,e',heq] at hdiff'
  change Tendsto (fun k =>
    r (k+N)^2*c k*(∫ x in ball (p (k+N)) (5*r (k+N)),
      θ k x*localGamma μ hX.quadratic (q k).val (q k).val x ∂μ)) atTop _ at hqenergy
  have htotal := hdiff'.add hqenergy
  simp only [zero_add,sub_add_cancel] at htotal
  exact (tendsto_add_atTop_iff_nat N).mp htotal

end RegularPointCoordinates

end

end OAI

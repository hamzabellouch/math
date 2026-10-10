import OAI.Geometry.RCD.Sobolev.RadialCutoffStrongComparison
import OAI.Geometry.RCD.Harmonic.LocalUniformDifference
import OAI.Geometry.RCD.Sobolev.WeightedBallEnergyLiminf

namespace OAI

/-! # Strong local comparison of an actual harmonic sequence and its recovery -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_recovery_strong_of_gradient_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S a b R T Q : ℝ} (hS : 0<S) (ha : 0<a) (hab : a<b) (hbR : b<R)
    (hRT : R<T) (hTS : T<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    {M : ℝ} (hM : 0≤M)
    (hwb : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (T*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M)
    (g F : Euclidean n → ℝ)
    (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (heq : EqOn F g (closedBall 0 T))
    (hd : EqOn (fderiv ℝ F) (fderiv ℝ g) (ball 0 T))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (V k x)|≤δ)
    (hqconv : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k) x-F (V k x)|≤δ)
    (hqg : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (q k) (q k) x≤Q^2)
    (hq : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), (euclideanNestedCutoff n hab (V k x))^2*
        localGamma (hausdorff n X) hX.quadratic (q k) (q k) x ∂hausdorff n X)
      atTop (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, (euclideanNestedCutoff n hab z)^2*‖fderiv ℝ F z‖^2))) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (R*r k), (nestedBallCutoff (p k) (a*r k) (b*r k) x)^2*
        localGamma (hausdorff n X) hX.quadratic (w k-q k) (w k-q k) x ∂hausdorff n X)
      atTop (𝓝 0) := by
  let μ := hausdorff n X
  let φ : Euclidean n →ᵇ ℝ := (euclideanNestedCutoff n hab)^2
  let ρ := (b+R)/2
  have hbρ : b<ρ := by dsimp only [ρ]; linarith
  have hρR : ρ<R := by dsimp only [ρ]; linarith
  have hR : 0<R := ha.trans (hab.trans hbR)
  have hφ : ∀ z, 0≤φ z := fun z => sq_nonneg _
  have hs : Function.support φ⊆ball 0 ρ := by
    intro z hz
    by_contra hx
    have hh : b≤dist (0:Euclidean n) z := by
      have : ρ≤dist z 0 := le_of_not_gt hx
      rw [dist_comm] at this
      exact hbρ.le.trans this
    have he := nestedBallCutoff_eq_zero (0:Euclidean n) hab hh
    change (euclideanNestedCutoff n hab z)^2≠0 at hz
    exact hz (by change (nestedBallCutoff (0:Euclidean n) a b z)^2=0; rw [he]; norm_num)
  have hφzero (z : Euclidean n) (hz : z∉ball 0 S) : φ z=0 :=
    Function.notMem_support.mp (fun h => hz ((ball_subset_ball (hρR.trans (hRT.trans hTS)).le) (hs h)))
  have hE : (∫ z, φ z*‖fderiv ℝ g z‖^2)=
      ∫ z in ball 0 S, φ z*‖fderiv ℝ F z‖^2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hφzero z hz,zero_mul])]
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    change φ z*‖fderiv ℝ g z‖^2=φ z*‖fderiv ℝ F z‖^2
    by_cases hzφ : φ z=0
    · rw [hzφ,zero_mul,zero_mul]
    · have hzρ := hs hzφ
      rw [hd ((ball_subset_ball (hρR.trans hRT).le) hzρ)]
  have hlow := hX.weighted_energy_eventual_lower_on_ball hn hS hR.le hρR hRT hTS
    p r ε V hr hcurv hε hε1 hεlim hV w g hg hconv φ hφ hs hM (Eventually.of_forall hwb)
  have hsub (k : ℕ) : ball (p k) (R*r k)⊆closedBall (p k) (T*r k) :=
    fun x hx => ball_subset_closedBall ((ball_subset_ball (mul_le_mul_of_nonneg_right hRT.le (hr k).le)) hx)
  have hwg : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (ball (p k) (R*r k)),
      r k^2*localGamma μ hX.quadratic (w k) (w k) x≤(M+1)^2 := by
    apply Eventually.of_forall
    intro k
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hsub k) (hwb k)] with x hx
    nlinarith
  have hvalue := hX.local_uniform_difference_l2 hS hRT hTS p r ε V hr hεlim hV w q g F heq
    (hconv R hR (hRT.trans hTS)) hqconv
  refine hX.radial_cutoff_strong_comparison hS hab hbR (hRT.trans hTS)
    (A := 0) (M := M+1) (Q := Q) (by norm_num) (by linarith) p r ε (fun _ => 0) V hr hεlim hV w q
    (Eventually.of_forall fun _ => by simp) ?_ hwg
    (hqg.mono fun k hk => ae_restrict_of_ae hk) hvalue hq ?_
  · intro k ψ hψ
    have hmem := (dirichlet_mono μ hX.quadratic
      (ball_subset_ball (mul_le_mul_of_nonneg_right (hRT.trans hTS).le (hr k).le))) hψ
    simpa only [zero_div,neg_zero,zero_mul] using hw k ψ hmem
  · intro δ hδ
    filter_upwards [hlow δ hδ] with k hk
    rw [hE] at hk
    simpa only [φ,BoundedContinuousFunction.pow_apply,div_eq_mul_inv] using hk

theorem NoncollapsedRCD.harmonic_recovery_strong {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S a b R T Q : ℝ} (hS : 0<S) (ha : 0<a) (hab : a<b) (hbR : b<R)
    (hRT : R<T) (hTS : T<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤1)
    (g F : Euclidean n → ℝ)
    (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (heq : EqOn F g (closedBall 0 T))
    (hd : EqOn (fderiv ℝ F) (fderiv ℝ g) (ball 0 T))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (V k x)|≤δ)
    (hqconv : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k) x-F (V k x)|≤δ)
    (hqg : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (q k) (q k) x≤Q^2)
    (hq : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), (euclideanNestedCutoff n hab (V k x))^2*
        localGamma (hausdorff n X) hX.quadratic (q k) (q k) x ∂hausdorff n X)
      atTop (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, (euclideanNestedCutoff n hab z)^2*‖fderiv ℝ F z‖^2))) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (R*r k), (nestedBallCutoff (p k) (a*r k) (b*r k) x)^2*
        localGamma (hausdorff n X) hX.quadratic (w k-q k) (w k-q k) x ∂hausdorff n X)
      atTop (𝓝 0) := by
  obtain ⟨M,hM,hwb⟩ := hX.harmonic_scaled_energy_bound hn hS (ha.le.trans (hab.le.trans (hbR.le.trans hRT.le))) hTS
    p r hr hcurv w hw hnorm
  exact hX.harmonic_recovery_strong_of_gradient_bound hn hS ha hab hbR hRT hTS
    p r ε V hr hcurv hε hε1 hεlim hV w q hw hM hwb g F hg heq hd hconv hqconv hqg hq

end RegularPointCoordinates

end

end OAI

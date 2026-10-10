import OAI.Geometry.RCD.Harmonic.HarmonicRecoveryStrong
import OAI.Geometry.RCD.Harmonic.SmoothHarmonicModelCompactness
import OAI.Geometry.RCD.Metric.EuclideanInteriorSmoothExtension
import OAI.Geometry.RCD.Sobolev.SharpWeightedTestRecovery
import OAI.Geometry.RCD.Sobolev.SmoothRecoveryGradientBound

namespace OAI

/-! # Constructed Dirichlet recoveries strongly approximate the harmonic sequence -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_strong_recovery {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S a b R T : ℝ} (hS : 0<S) (ha : 0<a) (hab : a<b) (hbR : b<R)
    (hRT : R<T) (hTS : T<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤1)
    (g : Euclidean n → ℝ) (hg : ContDiffOn ℝ ∞ g (ball 0 S))
    (hgL : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (V k x)|≤δ) :
    ∃ F : Euclidean n → ℝ, InteriorSmoothTest n S F ∧
      EqOn F g (closedBall 0 T) ∧ EqOn (fderiv ℝ F) (fderiv ℝ g) (ball 0 T) ∧
    ∃ N : ℕ, ∃ q : ∀ k : ℕ,
      SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball (p (k+N)) (S*r (k+N))),
      (∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (S*r (k+N))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k).val x-F (V (k+N) x)|≤δ) ∧
      (∃ Q : ℝ, 0≤Q ∧ ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
        r (k+N)^2*localGamma (hausdorff n X) hX.quadratic (q k).val (q k).val x≤Q^2) ∧
      (∀ φ : Euclidean n →ᵇ ℝ, (∀ z, 0≤φ z) → tsupport φ⊆ball 0 S →
        Tendsto (fun k => r (k+N)^2*((hausdorff n X).real (ball (p (k+N)) (S*r (k+N))))⁻¹*
          ∫ x in ball (p (k+N)) (S*r (k+N)), φ (V (k+N) x)*localGamma (hausdorff n X) hX.quadratic
            (q k).val (q k).val x ∂hausdorff n X) atTop
          (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
            ∫ z in ball 0 S, φ z*‖fderiv ℝ F z‖^2))) ∧
      Tendsto (fun k => r (k+N)^2*((hausdorff n X).real (ball (p (k+N)) (S*r (k+N))))⁻¹*
        ∫ x in ball (p (k+N)) (R*r (k+N)),
          (nestedBallCutoff (p (k+N)) (a*r (k+N)) (b*r (k+N)) x)^2*
          localGamma (hausdorff n X) hX.quadratic (w (k+N)-(q k).val) (w (k+N)-(q k).val) x
          ∂hausdorff n X) atTop (𝓝 0) := by
  obtain ⟨F,hF,heq,hd⟩ := exists_interior_smooth_extension
    (ha.trans (hab.trans (hbR.trans hRT))) hTS hg
  obtain ⟨c,hc,hcS,N,q,hqv,hqg,hqz,hqe⟩ :=
    hX.sharp_weighted_test_recovery hn hS p r ε V hr hcurv hε hε1 hεlim hV hF
  obtain ⟨Q,hQ,hQb⟩ := compact_recovery_scaled_gradient_bound (hausdorff n X) hX.quadratic
    (hF.1.of_le (by simp)) hF.2.1 (fun k => p (k+N)) (fun k => r (k+N))
    (fun k => hr (k+N)) (fun k => V (k+N)) (fun k => (q k).val) hqz (hqg c hc.le hcS)
  refine ⟨F,hF,heq,hd,N,q,hqv,⟨Q,hQ,hQb⟩,hqe,?_⟩
  apply hX.harmonic_recovery_strong hn hS ha hab hbR hRT hTS
    (fun k => p (k+N)) (fun k => r (k+N)) (fun k => ε (k+N)) (fun k => V (k+N))
    (fun k => hr (k+N)) (fun k => hcurv (k+N)) (fun k => hε (k+N)) (fun k => hε1 (k+N))
    (hεlim.comp (tendsto_add_atTop_nat N)) (fun k => hV (k+N))
    (fun k => w (k+N)) (fun k => (q k).val) (fun k => hw (k+N)) (fun k => hnorm (k+N))
    g F hgL heq hd
    (fun W hW hWS δ hδ => (tendsto_add_atTop_nat N).eventually (hconv W hW hWS δ hδ)) hqv hQb
  let φ : Euclidean n →ᵇ ℝ := (euclideanNestedCutoff n hab)^2
  apply hqe φ (fun z => sq_nonneg _) ?_
  have hs : tsupport φ⊆closedBall (0:Euclidean n) b := by
    change closure (Function.support φ)⊆closedBall 0 b
    apply closure_minimal _ isClosed_closedBall
    intro z hz
    by_contra hx
    have hz' : b<dist (0:Euclidean n) z := by simpa only [mem_closedBall,not_le,dist_comm] using hx
    have he := nestedBallCutoff_eq_zero (0:Euclidean n) hab hz'.le
    exact hz (by change (nestedBallCutoff (0:Euclidean n) a b z)^2=0; rw [he]; norm_num)
  exact hs.trans (closedBall_subset_ball (hbR.trans (hRT.trans hTS)))

end RegularPointCoordinates

end

end OAI

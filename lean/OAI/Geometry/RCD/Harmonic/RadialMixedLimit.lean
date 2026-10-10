import OAI.Geometry.RCD.Harmonic.RadialMixedRecoveryLimit
import OAI.Geometry.RCD.Harmonic.HarmonicStrongRecovery

namespace OAI

/-! # Actual radial mixed-gradient convergence with the original physical measures

The compact recoveries below are constructed from the RCD data. Their
finite initial shifts depend on the chosen test, and are removed before
stating the limit for the original, fixed harmonic sequence.
-/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal ContDiff
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.radial_mixed_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S : ℝ} (hS : 0<S) (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (f w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤1)
    (g : Euclidean n → ℝ) (hg : ContDiffOn ℝ ∞ g (ball 0 S))
    (hgL : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (V k x)|≤δ)
    {A : ℝ} (hA : 0≤A)
    (hfb : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (f k) (f k) x≤A^2)
    (hflim : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic (f k) x-‖V k x‖^2/2)^2
        ∂hausdorff n X) atTop (𝓝 0))
    {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), ψ (V k x)*localGamma (hausdorff n X) hX.quadratic
        (f k) (w k) x ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, ψ z*fderiv ℝ g z z)) := by
  have hweak := hX.harmonic_value_limit_weak_of_curvature hn hS p r ε hr hcurv hε hε1 hεlim
    V w hV hw hnorm g hgL hconv
  obtain ⟨d,hd,hds⟩ := exists_pos_lt_subset_ball hS (isClosed_tsupport ψ) hψ.2.2
  obtain ⟨c₀,hc₀,hc₀S,N,u,huv,hug,huz,hue⟩ :=
    hX.sharp_weighted_test_recovery hn hS p r ε V hr hcurv hε hε1 hεlim hV hψ
  obtain ⟨Q,hQ,hub⟩ := compact_recovery_scaled_gradient_bound (hausdorff n X) hX.quadratic
    (hψ.1.of_le (by simp)) hψ.2.1 (fun k => p (k+N)) (fun k => r (k+N))
    (fun k => hr (k+N)) (fun k => V (k+N)) (fun k => (u k).val) huz (hug c₀ hc₀.le hc₀S)
  let c := max d c₀
  have hc : 0<c := hd.1.trans_le (le_max_left _ _)
  have hcS : c<S := max_lt hd.2 hc₀S
  let a := (5*c+S)/6
  let b := (4*c+2*S)/6
  let R := (3*c+3*S)/6
  let T := (2*c+4*S)/6
  have hca : c<a := by dsimp only [a]; linarith
  have hab : a<b := by dsimp only [a,b]; linarith
  have hbR : b<R := by dsimp only [b,R]; linarith
  have hRT : R<T := by dsimp only [R,T]; linarith
  have hTS : T<S := by dsimp only [T]; linarith
  have ha : 0<a := hc.trans hca
  have hT : 0<T := ha.trans (hab.trans (hbR.trans hRT))
  obtain ⟨G,hG,_,hdG,M,q,hqv,⟨P,_hP,hqb⟩,hqe,herror⟩ :=
    hX.harmonic_strong_recovery hn hS ha hab hbR hRT hTS
      (fun k => p (k+N)) (fun k => r (k+N)) (fun k => ε (k+N)) (fun k => V (k+N))
      (fun k => hr (k+N)) (fun k => hcurv (k+N)) (fun k => hε (k+N)) (fun k => hε1 (k+N))
      (hεlim.comp (tendsto_add_atTop_nat N)) (fun k => hV (k+N))
      (fun k => w (k+N)) (fun k => hw (k+N)) (fun k => hnorm (k+N)) g hg hgL
      (fun W hW hWS δ hδ => (tendsto_add_atTop_nat N).eventually (hconv W hW hWS δ hδ))
  obtain ⟨F,hF,hFn,hFr,_⟩ := exists_compact_radial_weight (n:=n) hT hTS
  let j := fun k : ℕ => (k+M)+N
  have hj : Tendsto j atTop atTop := (tendsto_add_atTop_nat N).comp (tendsto_add_atTop_nat M)
  obtain ⟨B,hB,hwb⟩ := hX.harmonic_scaled_energy_bound hn hS hT.le hTS
    (p ∘ j) (r ∘ j) (fun k => hr (j k)) (fun k => hcurv (j k))
    (w ∘ j) (fun k => hw (j k)) (fun k => hnorm (j k))
  have hwb' : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (j k)) (T*r (j k))),
      r (j k)^2*localGamma (hausdorff n X) hX.quadratic (w (j k)) (w (j k)) x≤(B+1)^2 := by
    apply Eventually.of_forall
    intro k
    have hh := ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall (hwb k)
    exact hh.mono fun x hx => hx.trans (by nlinarith)
  have hfb' : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (j k)) (T*r (j k))),
      r (j k)^2*localGamma (hausdorff n X) hX.quadratic (f (j k)) (f (j k)) x≤A^2 := by
    apply Eventually.of_forall
    intro k
    exact ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (mul_le_mul_of_nonneg_right hTS.le (hr (j k)).le)) (hfb (j k))
  have huz' (k : ℕ) : ∀ᵐ x ∂hausdorff n X, x∉ball (p (j k)) (c*r (j k)) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (u (k+M)).val x=0 :=
    (huz (k+M)).mono fun x hx hn' => hx (fun hy => hn'
      ((ball_subset_ball (mul_le_mul_of_nonneg_right (le_max_right d c₀) (hr (j k)).le)) hy))
  have ht := hX.radial_mixed_recovery_limit hn hS hca hab hbR hRT hTS
    (p ∘ j) (r ∘ j) (ε ∘ j) (fun k => V (j k))
    (fun k => hr (j k)) (fun k => hcurv (j k)) (fun k => hε (j k)) (fun k => hε1 (j k))
    (hεlim.comp hj) (fun k => hV (j k)) (f ∘ j) (w ∘ j) (fun k => (u (k+M)).val)
    (fun k => (q k).val) (fun k => hw (j k)) hgL hweak hG hdG hψ
    (hds.trans (ball_subset_ball (le_max_left _ _)))
    (fun δ hδ => (tendsto_add_atTop_nat M).eventually (huv δ hδ)) hqv huz'
    hA (by linarith : 0≤B+1) hQ hfb' hwb'
    ((tendsto_add_atTop_nat M).eventually hub) hqb F hF hFn hFr
    ((hue F hFn hF.2.2).comp (tendsto_add_atTop_nat M)) (hqe F hFn hF.2.2)
    herror (hflim.comp hj)
  exact (tendsto_add_atTop_iff_nat N).mp ((tendsto_add_atTop_iff_nat M).mp ht)

end RegularPointCoordinates

end

end OAI

import OAI.Geometry.RCD.Coordinates.NormalizedRecoveryRadialSwap
import OAI.Geometry.RCD.Harmonic.CompactRecoveryCoefficient
import OAI.Geometry.RCD.Harmonic.CompactHarmonicTransfer
import OAI.Geometry.RCD.Sobolev.CompactRecoveryMixedEnergy
import OAI.Geometry.RCD.Harmonic.CompactRadialPairingIdentity

namespace OAI

/-! # The radial mixed-gradient limit from the constructed compact recoveries -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.radial_mixed_recovery_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S c a b R T : ℝ} (hS : 0<S) (hca : c<a) (hab : a<b) (hbR : b<R)
    (hRT : R<T) (hTS : T<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (f w u q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    {g G ψ : Euclidean n → ℝ}
    (hgL : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hgweak : EuclideanWeakHarmonicOn g S)
    (hG : InteriorSmoothTest n S G) (hd : EqOn (fderiv ℝ G) (fderiv ℝ g) (ball 0 T))
    (hψ : InteriorSmoothTest n S ψ) (hψs : tsupport ψ⊆ball 0 c)
    (huv : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-ψ (V k x)|≤δ)
    (hqv : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (S*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (q k) x-G (V k x)|≤δ)
    (huz : ∀ k, ∀ᵐ x ∂hausdorff n X, x∉ball (p k) (c*r k) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x=0)
    {A M Q P : ℝ} (hA : 0≤A) (hM : 0≤M) (hQ : 0≤Q)
    (hfb : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (T*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (f k) (f k) x≤A^2)
    (hwb : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (T*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M^2)
    (hub : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (u k) (u k) x≤Q^2)
    (hqb : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (q k) (q k) x≤P^2)
    (F : Euclidean n →ᵇ ℝ) (hF : InteriorSmoothTest n S F) (hFn : ∀ z, 0≤F z)
    (hFr : EqOn F (fun z => ‖z‖^2/2) (closedBall 0 T))
    (hue : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), F (V k x)*localGamma (hausdorff n X) hX.quadratic
        (u k) (u k) x ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*∫ z in ball 0 S, F z*‖fderiv ℝ ψ z‖^2)))
    (hqe : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), F (V k x)*localGamma (hausdorff n X) hX.quadratic
        (q k) (q k) x ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*∫ z in ball 0 S, F z*‖fderiv ℝ G z‖^2)))
    (herror : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (R*r k), (nestedBallCutoff (p k) (a*r k) (b*r k) x)^2*
        localGamma (hausdorff n X) hX.quadratic (w k-q k) (w k-q k) x ∂hausdorff n X)
      atTop (𝓝 0))
    (hflim : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic (f k) x-‖V k x‖^2/2)^2
        ∂hausdorff n X) atTop (𝓝 0)) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), ψ (V k x)*localGamma (hausdorff n X) hX.quadratic
        (f k) (w k) x ∂hausdorff n X) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*
        ∫ z in ball 0 S, ψ z*fderiv ℝ g z z)) := by
  let μ := hausdorff n X
  let : ∀ k, IsFiniteMeasure (μ.restrict (ball (p k) (S*r k))) := fun k => ⟨by
    simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded _ isBounded_ball⟩
  have hcT := hca.trans (hab.trans (hbR.trans hRT))
  obtain ⟨B,hB⟩ := hψ.2.1.exists_bound_of_continuous hψ.1.continuous
  have hcoeff := compact_recovery_coefficient μ hX.quadratic hS hcT hcT hTS p r ε V hr hεlim hV
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne) u f w ψ hψ.1.continuous
    (fun x => by simpa only [Real.norm_eq_abs] using hB x) hψs huz huv hA hM hfb hwb
  have hswap := hX.normalized_recovery_radial_swap hn hS hcT hTS p r ε V hr hεlim hV
    f w u hw hQ hM hub hwb huz F hFr hflim
  have htransfer := hX.compact_harmonic_transfer hS hca hab hbR (hRT.trans hTS) p r hr V
    (fun k => (hV k).measurable) u w q F hub huz herror
  have hmix := hX.compact_recovery_mixed_energy hn hS p r ε V hr hcurv hε hε1 hεlim hV
    u q hψ hG huv hqv (sq_nonneg Q) (sq_nonneg P) hub hqb F hFn hF.2.2 hue hqe
  have hid := compact_radial_pairing_identity hS hTS F hgL hgweak hG.1 hd hFr hψ
    (hψs.trans (ball_subset_ball hcT.le))
  rw [hid,mul_neg] at hmix
  have ht := ((hcoeff.add hswap).sub htransfer).sub hmix
  convert ht using 1
  · funext k
    ring
  · simp

end RegularPointCoordinates

end

end OAI

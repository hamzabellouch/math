import OAI.Geometry.RCD.Harmonic.RecoveryHarmonicSwap
import OAI.Geometry.RCD.Sobolev.SupportedGradientL2Error
import OAI.Geometry.RCD.Coordinates.CompactRadialPullback
import OAI.Geometry.RCD.Sobolev.ScaledGradientGammaL2

namespace OAI

/-! # Harmonicity replaces the Poisson gradient by its radial value limit -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.normalized_recovery_radial_swap {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S c T : ℝ} (hS : 0<S) (hcT : c<T) (hTS : T<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (f w u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (w k))
    {Q M : ℝ} (hQ : 0≤Q) (hM : 0≤M)
    (hu : ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      r k^2*localGamma (hausdorff n X) hX.quadratic (u k) (u k) x≤Q^2)
    (hwb : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (T*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M^2)
    (hz : ∀ k, ∀ᵐ x ∂hausdorff n X, x∉ball (p k) (c*r k) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x=0)
    (F : Euclidean n →ᵇ ℝ) (hF : EqOn F (fun z => ‖z‖^2/2) (closedBall 0 T))
    (hlim : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic (f k) x-‖V k x‖^2/2)^2
        ∂hausdorff n X) atTop (𝓝 0)) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (S*r k), SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x*
        localGamma (hausdorff n X) hX.quadratic (f k) (w k) x ∂hausdorff n X)+
      r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      (∫ x in ball (p k) (S*r k), F (V k x)*
        localGamma (hausdorff n X) hX.quadratic (u k) (w k) x ∂hausdorff n X))
      atTop (𝓝 0) := by
  let μ := hausdorff n X
  let U := fun k => ball (p k) (S*r k)
  let Ω := fun k => ball (p k) (T*r k)
  let z := fun k x => SobolevSpace.toLp μ hX.quadratic (f k) x-‖V k x‖^2/2
  let : ∀ k, IsFiniteMeasure (μ.restrict (U k)) := fun k =>
    ⟨by rw [Measure.restrict_apply_univ]; exact hX.finiteOnBounded (U k) isBounded_ball⟩
  have hrad (k : ℕ) : MemLp (fun x => ‖V k x‖^2/2) 2 (μ.restrict (U k)) :=
    measured_radial_memLp μ (hr k) hS.le (V k) (hV k)
  have hzL (k : ℕ) : MemLp (z k) 2 (μ.restrict (U k)) :=
    ((Lp.memLp (SobolevSpace.toLp μ hX.quadratic (f k))).restrict (U k)).sub (hrad k)
  have huT : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      r k^2*localGamma μ hX.quadratic (u k) (u k) x≤Q^2 :=
    hu.mono fun _ hk => ae_restrict_of_ae hk
  have huz (k : ℕ) : ∀ᵐ x ∂μ, x∉Ω k → SobolevSpace.toLp μ hX.quadratic (u k) x=0 :=
    (hz k).mono fun x hx hy => hx (fun hh => hy
      ((ball_subset_ball (mul_le_mul_of_nonneg_right hcT.le (hr k).le)) hh))
  have he := supported_gradient_l2_error μ hX.quadratic Ω U
    (fun k => ball_subset_ball (mul_le_mul_of_nonneg_right hTS.le (hr k).le))
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne) r (fun k => (hr k).le)
    u w z hQ hM huT hwb huz hzL hlim
  have hweight := compact_radial_pullback μ hX.quadratic hS hcT hTS p r ε V hr hε hV u w hz F hF
  have heq : ∀ᶠ k in atTop,
      r k^2*(μ.real (U k))⁻¹*(∫ x in U k, SobolevSpace.toLp μ hX.quadratic (u k) x*
        localGamma μ hX.quadratic (f k) (w k) x ∂μ)+
      r k^2*(μ.real (U k))⁻¹*(∫ x in U k, F (V k x)*
        localGamma μ hX.quadratic (u k) (w k) x ∂μ)=
      -(r k^2*(μ.real (U k))⁻¹*∫ x in U k, z k x*localGamma μ hX.quadratic (u k) (w k) x ∂μ) := by
    filter_upwards [hu,hweight] with k huk hwk
    have hγ := scaled_gradient_gamma_memLp μ hX.quadratic (u k) (w k) (hr k) hQ huk
    have hi := ((Lp.memLp (SobolevSpace.toLp μ hX.quadratic (f k))).restrict (U k)).integrable_mul
      (hγ.restrict (U k))
    have hj := (hrad k).integrable_mul (hγ.restrict (U k))
    have hs := hX.recovery_harmonic_swap hn (f k) (w k) (u k) (p k) (hr k)
      (hcT.trans hTS) hQ huk (hz k) (hw k)
    change (∫ x in U k, _ ∂μ)=_ at hs
    rw [hs]
    have hrw : (∫ x in U k, F (V k x)*localGamma μ hX.quadratic (u k) (w k) x ∂μ)=
        ∫ x in U k, (‖V k x‖^2/2)*localGamma μ hX.quadratic (u k) (w k) x ∂μ :=
      integral_congr_ae (ae_restrict_of_ae hwk.symm)
    rw [hrw]
    have hsub : (∫ x in U k, z k x*localGamma μ hX.quadratic (u k) (w k) x ∂μ)=
        (∫ x in U k, SobolevSpace.toLp μ hX.quadratic (f k) x*localGamma μ hX.quadratic (u k) (w k) x ∂μ)-
        (∫ x in U k, (‖V k x‖^2/2)*localGamma μ hX.quadratic (u k) (w k) x ∂μ) := by
      simp only [z,sub_mul]
      exact integral_sub hi hj
    rw [hsub]
    ring
  simpa only [neg_zero] using he.neg.congr' (heq.mono fun _ hk => hk.symm)

end RegularPointCoordinates

end

end OAI

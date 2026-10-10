import OAI.Geometry.RCD.Sobolev.FullBochnerMassBound
import OAI.Geometry.RCD.Heat.HeatMixedGramEnergy

namespace OAI

/-! # The actual bounded heat test has a quantitative full Bochner mass -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_full_mass_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (p : X) {r s C : ℝ} (hr : 0 < r) (hs : 0 < s) (hC : 0 ≤ C)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p r C)
    (h : Lp ℝ 2 (hausdorff n X)) (V : X → ℝ) (L A : ℝ≥0)
    (hV : LipschitzWith L V) (hVc : HasCompactSupport V)
    (hrep : V =ᵐ[hausdorff n X] h)
    (hA : ∀ᵐ x ∂hausdorff n X, |h x|≤A)
    (H : SobolevSpace (hausdorff n X) hX.quadratic)
    (hH : SobolevSpace.toLp (hausdorff n X) hX.quadratic H =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic s hs h)
        (heatSobolev (hausdorff n X) hX.quadratic s hs h))
    {Ω : Set X} (hΩ : tsupport (χ.weight : X → ℝ) ⊆ Ω)
    (τ : Measure X) [IsFiniteMeasure τ]
    (hτ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic Ω H
      (bochnerGramSource (hausdorff n X) hX.quadratic K
        (heatSobolev (hausdorff n X) hX.quadratic s hs h)
        (heatSobolev (hausdorff n X) hX.quadratic s hs h)
        (heatSobolevMap (hausdorff n X) hX.quadratic (s/2) (half_pos hs)
          (-heatGeneratorAt (hausdorff n X) hX.quadratic (s-s/2) h))
        (heatSobolevMap (hausdorff n X) hX.quadratic (s/2) (half_pos hs)
          (-heatGeneratorAt (hausdorff n X) hX.quadratic (s-s/2) h)) τ.toSignedMeasure)) :
    let ℓ := (L:ℝ)*Real.exp (-K*s)
    let b := (2*(n:ℝ)*(|K|+1/s))*(A:ℝ)
    τ.real (ball p r)≤((C/r^2)/2*ℓ^2+(-K)*ℓ^2+b^2+b*ℓ*(C/r))*
      (hausdorff n X).real (closedBall p (2*r)) := by
  intro ℓ b
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let w := heatSobolev μ Q s hs h
  let d := heatSobolevMap μ Q (s/2) (half_pos hs) (-heatGeneratorAt μ Q (s-s/2) h)
  let L' : ℝ≥0 := ⟨ℓ,mul_nonneg L.coe_nonneg (Real.exp_pos _).le⟩
  let B : ℝ≥0 := ⟨b,by dsimp only [b]; positivity⟩
  have hw : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q w x≤L' :=
    hX.heat_compact_slope_bdd K n hn hV hVc p h hrep s hs
  have hdt : SobolevSpace.toLp μ Q d = -heatGeneratorAt μ Q s h :=
    heatTail_deriv_toLp μ Q (s/2) (half_pos hs) h s (by linarith)
  have hd : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q d x|≤B := by
    rw [hdt]
    filter_upwards [hX.heatGeneratorAt_amplitude hn p hK h A hA hs,
      Lp.coeFn_neg (heatGeneratorAt μ Q s h)] with x hx he
    rw [he]
    change |-heatGeneratorAt μ Q s h x|≤b
    simpa only [abs_neg] using hx
  exact χ.regular_full_mass_bound μ Q hr hC hK w d H (heatTail_weak_laplacian μ Q s hs h)
    hH hΩ τ hτ L' B (ae_restrict_of_ae hw) (ae_restrict_of_ae hd)

end RegularPointCoordinates

end

end OAI

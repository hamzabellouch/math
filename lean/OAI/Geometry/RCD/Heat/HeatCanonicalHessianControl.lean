import OAI.Geometry.RCD.Sobolev.CurvedCanonicalHessianMass
import OAI.Geometry.RCD.Heat.HeatGeneratorAmplitude

namespace OAI

/-! # The actual heat regularization satisfies the canonical Hessian mass bound -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem heat_canonical_hessian_young (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hA : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (G : SobolevSpace (hausdorff n X) hX.quadratic)
    (σ : Measure X) [IsFiniteMeasure σ]
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic s hs f)
        (heatSobolev (hausdorff n X) hX.quadratic s hs f))
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) G
      (bochnerGramSource (hausdorff n X) hX.quadratic K
        (heatSobolev (hausdorff n X) hX.quadratic s hs f)
        (heatSobolev (hausdorff n X) hX.quadratic s hs f)
        (heatSobolevMap (hausdorff n X) hX.quadratic (s/2) (half_pos hs)
          (-heatGeneratorAt (hausdorff n X) hX.quadratic (s-s/2) f))
        (heatSobolevMap (hausdorff n X) hX.quadratic (s/2) (half_pos hs)
          (-heatGeneratorAt (hausdorff n X) hX.quadratic (s-s/2) f)) σ.toSignedMeasure))
    (v : SobolevSpace (hausdorff n X) hX.quadratic) (V : X → ℝ) (Lv Av : ℝ≥0)
    (hV : LipschitzWith Lv V) (hVc : HasCompactSupport V)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hAv : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ Av)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (Dφ : ℝ≥0)
    (hDφ : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ Dφ)
    (J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)))
    (hJ : IsCanonicalHeatHessian (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic s hs f) v p r φ J)
    {a : ℝ} (ha : 0 < a) :
    4*a*(∫ x in closedBall p r, |J x| ∂hausdorff n X) ≤
      4*a^2*(hausdorff n X).real (closedBall p r)+
        ((Dφ:ℝ)*((Lv:ℝ)*Real.exp |K|)^2)^2*σ.real (closedBall p r) := by
  let m := hausdorff n X
  let q := hX.quadratic
  let w := heatSobolev m q s hs f
  let D := heatSobolevMap m q (s/2) (half_pos hs) (-heatGeneratorAt m q (s-s/2) f)
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨hLip,-⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hA s hs
  have hwr : SobolevSpace.toLp m q w =ᵐ[m] kernelHeat m q hk s f := by
    simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 m q hk hs f).symm
  have hD : SobolevSpace.toLp m q D = -heatGeneratorAt m q s f :=
    heatTail_deriv_toLp m q (s/2) (half_pos hs) f s (by linarith [hs])
  let B : ℝ≥0 := ⟨(2*(n:ℝ)*(|K|+1/s))*(A:ℝ),by have := hs; positivity⟩
  have hdB : ∀ᵐ x ∂m, |SobolevSpace.toLp m q D x| ≤ B := by
    rw [hD]
    filter_upwards [hX.heatGeneratorAt_amplitude hn p hK f A hA hs,
      Lp.coeFn_neg (heatGeneratorAt m q s f)] with x hx he
    rw [he]
    change |-(heatGeneratorAt m q s f x)| ≤ (2*(n:ℝ)*(|K|+1/s))*(A:ℝ)
    simpa only [abs_neg] using hx
  exact hX.curved_canonical_hessian_young_bound hn p hK w D G
    (heatTail_weak_laplacian m q s hs f) (kernelHeat m q hk s f) _ A B
    hLip hwr (hX.bounded_heat_sobolev_data hn p f A hA hs).1 hdB hG hr σ hσ
    v V Lv Av hV hVc hv hAv φ hφ Dφ hDφ J hJ ha

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

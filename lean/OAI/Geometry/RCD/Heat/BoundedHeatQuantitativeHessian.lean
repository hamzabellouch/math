import OAI.Geometry.RCD.Coordinates.BoundedRegularPrescribedHessian
import OAI.Geometry.RCD.Coordinates.BoundedRegularBochnerMass
import OAI.Geometry.RCD.Sobolev.BochnerMeasureFromSource
import OAI.Geometry.RCD.Heat.BoundedHeatGram
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData
import OAI.Geometry.RCD.Heat.HeatGeneratorAmplitude
import OAI.Geometry.RCD.Heat.HeatIteratedLaplacian
import OAI.Geometry.RCD.Sobolev.ScalarBochnerConstruction

namespace OAI

/-! # Quantitative local Bochner measures for the actual heat Hessian

One coefficient controls every radius. The very same measures dominate
all bounded regular direction pairs, with their singular mass retained.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2≤n) (p : X)

include hn p in
theorem bounded_heat_quantitative_hessian (hK : K≤0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) {a : ℝ} (ha : 0<a) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let w := heatSobolev m Q a ha f
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r → ∃ (σ : Measure X) (_ : IsFiniteMeasure σ),
      σ.real (closedBall p r) ≤ M*Real.sqrt ((1+r⁻¹^2)*m.real (closedBall p (2*r))) ∧
      ∀ (g : SobolevSpace m Q) (q : Lp ℝ 2 m), IsWeakLaplacian m Q g q →
      ∀ (V : X → ℝ) (M C : ℝ≥0), LipschitzWith M V →
      (SobolevSpace.toLp m Q g =ᵐ[m] V) →
      (∀ᵐ x ∂m, |SobolevSpace.toLp m Q g x|≤C) →
      ∀ (v : SobolevSpace m Q) (e : Lp ℝ 2 m), IsWeakLaplacian m Q v e →
      ∀ (Z : X → ℝ) (N D : ℝ≥0), LipschitzWith N Z →
      (SobolevSpace.toLp m Q v =ᵐ[m] Z) →
      (∀ᵐ x ∂m, |SobolevSpace.toLp m Q v x| ≤ D) →
      ∃ WG WV GV : SobolevSpace m Q,
        (SobolevSpace.toLp m Q WG =ᵐ[m.restrict (closedBall p r)] localGamma m Q w g) ∧
        (SobolevSpace.toLp m Q WV =ᵐ[m.restrict (closedBall p r)] localGamma m Q w v) ∧
        (SobolevSpace.toLp m Q GV =ᵐ[m.restrict (closedBall p r)] localGamma m Q g v) ∧
        ∀ᵐ x ∂m.restrict (closedBall p r),
          (localHessianAction m Q w g v WG WV GV x)^2 ≤
            (σ.rnDeriv m x).toReal*localGamma m Q g g x*localGamma m Q v v x := by
  intro m Q w
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hwr : SobolevSpace.toLp m Q w =ᵐ[m] kernelHeat m Q hk a f := by
    simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 m Q hk ha f).symm
  obtain ⟨hLip,-⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hf a ha
  obtain ⟨hwA,-⟩ := hX.bounded_heat_sobolev_data hn p f A hf ha
  obtain ⟨dw,hdw,-⟩ := heat_generator_iterated_laplacian m Q f ha
  have hw : IsWeakLaplacian m Q w (SobolevSpace.toLp m Q dw) := by
    rw [hdw,heatGeneratorAt_of_pos m Q a ha]
    exact heatSobolev_weak_laplacian m Q a ha f
  let B : ℝ≥0 := ⟨(2*(n:ℝ)*(|K|+1/a))*(A:ℝ),by positivity⟩
  have hdB : ∀ᵐ x ∂m, |SobolevSpace.toLp m Q dw x|≤B := by
    rw [hdw]
    change ∀ᵐ x ∂m, |(-heatGeneratorAt m Q a f) x|≤(2*(n:ℝ)*(|K|+1/a))*(A:ℝ)
    filter_upwards [hX.heatGeneratorAt_amplitude hn p hK f A hf ha,
      Lp.coeFn_neg (heatGeneratorAt m Q a f)] with x hx he
    rw [he]
    simpa only [Pi.neg_apply,abs_neg] using hx
  obtain ⟨G,hG⟩ := hX.bounded_heat_gram hn p f A hf ha
  obtain ⟨M,hM,hmeasure⟩ := hX.bounded_regular_bochner_mass hn hK p w dw G hw
    (kernelHeat m Q hk a f) hLip hwr A hwA hG
  refine ⟨M,hM,?_⟩
  intro r hr
  obtain ⟨σ,hσ,hrep,hmass⟩ := hmeasure r hr
  let := hσ
  have hlap := bochner_measure_laplacian_of_source m Q K w dw G hG σ hrep
  have hlap2 : IsMeasureLaplacianOn m Q (ball p (2*r)) G
      (bochnerGramSource m Q K w w dw dw σ.toSignedMeasure) := by
    intro ψ v hv hvc hvs hψ
    exact hlap ψ v hv hvc (hvs.trans (ball_subset_ball (by linarith))) hψ
  refine ⟨σ,hσ,hmass,?_⟩
  exact hX.bounded_regular_prescribed_hessian hn (hX.scalarBochner_nonpositive K n hn hK p)
    w dw hw (kernelHeat m Q hk a f) hLip hwr hwA hdB G hG p hr σ hlap2

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

import OAI.Geometry.RCD.Coordinates.BoundedRegularGramEnergy
import OAI.Geometry.RCD.Heat.BoundedHeatFullSource
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData
import OAI.Geometry.RCD.Heat.HeatGeneratorAmplitude
import OAI.Geometry.RCD.Sobolev.BochnerMeasureFromSource

namespace OAI

/-! # Actual heat-test mixed coefficients with the same full Bochner masses -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_mixed_gram_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (p : X) (f : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (qf : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (htr : t < 2*r)
    (hq0 : qf =ᵐ[(hausdorff n X).restrict (ball p (2*r))] fun _ => 0)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f.val f.val)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) F₀
      (bochnerGramSource (hausdorff n X) hX.quadratic K f.val f.val 0 0 σ.toSignedMeasure))
    (h : Lp ℝ 2 (hausdorff n X)) (A Cf Ca : ℝ≥0)
    (hA : ∀ᵐ x ∂hausdorff n X, |h x|≤A)
    (hCf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic f.val f.val x≤(Cf:ℝ)^2)
    (hCa : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic s hs h)
        (heatSobolev (hausdorff n X) hX.quadratic s hs h) x≤(Ca:ℝ)^2) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let w := heatSobolev μ Q s hs h
    let d := heatSobolevMap μ Q (s/2) (half_pos hs) (-heatGeneratorAt μ Q (s-s/2) h)
    ∃ (H G : SobolevSpace μ Q) (τ : Measure X) (hτ : IsFiniteMeasure τ),
      letI := hτ;
      (SobolevSpace.toLp μ Q H =ᵐ[μ] localGamma μ Q w w) ∧
      IsMeasureLaplacianOn μ Q (ball p (2*r)) H (bochnerGramSource μ Q K w w d d τ.toSignedMeasure) ∧
      (SobolevSpace.toLp μ Q G =ᵐ[μ.restrict (ball p (2*r))] localGamma μ Q f.val w) ∧
      (∫ x in ball p t, localGamma μ Q G G x ∂μ)≤
        2*(Ca:ℝ)^2*σ.real (ball p t)+2*(Cf:ℝ)^2*τ.real (ball p t) := by
  intro μ Q w d
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨hLip,_⟩ := hX.kernelHeat_bounded_regularity hn p hk h A hA s hs
  have hw : SobolevSpace.toLp μ Q w =ᵐ[μ] kernelHeat μ Q hk s h := by
    simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 μ Q hk hs h).symm
  have hWA := (hX.bounded_heat_sobolev_data hn p h A hA hs).1
  have hd : IsWeakLaplacian μ Q w (SobolevSpace.toLp μ Q d) := heatTail_weak_laplacian μ Q s hs h
  have hdt : SobolevSpace.toLp μ Q d = -heatGeneratorAt μ Q s h :=
    heatTail_deriv_toLp μ Q (s/2) (half_pos hs) h s (by linarith)
  let B : ℝ≥0 := ⟨(2*(n:ℝ)*(|K|+1/s))*(A:ℝ),by positivity⟩
  have hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q d x|≤B := by
    rw [hdt]
    filter_upwards [hX.heatGeneratorAt_amplitude hn p hK h A hA hs,
      Lp.coeFn_neg (heatGeneratorAt μ Q s h)] with x hx he
    rw [he]
    change |-heatGeneratorAt μ Q s h x| ≤ (2*(n:ℝ)*(|K|+1/s))*(A:ℝ)
    simpa only [abs_neg] using hx
  obtain ⟨H,τ,hτ,hH,hτsource⟩ := hX.bounded_heat_full_source hn hK p h A hA hs hr
  let := hτ
  obtain ⟨G,hG,henergy⟩ := hX.bounded_regular_gram_energy hn hK f qf hqf w d hd
    (kernelHeat μ Q hk s h) hLip hw hWA hB p hr ht htr hq0 F₀ H σ τ hF₀
    (ae_restrict_of_ae hH) hσ hτsource Cf Ca hCf hCa
  exact ⟨H,G,τ,hτ,hH,hτsource,hG,henergy⟩

end RegularPointCoordinates

end

end OAI

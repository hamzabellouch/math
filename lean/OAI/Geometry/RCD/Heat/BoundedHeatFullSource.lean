import OAI.Geometry.RCD.Coordinates.BoundedRegularBochnerMass
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData
import OAI.Geometry.RCD.Sobolev.BochnerMeasureFromSource

namespace OAI

/-! # One full local Bochner source for the actual bounded heat test -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_heat_full_source {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (p : X) (h : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hA : ∀ᵐ x ∂hausdorff n X, |h x|≤A) {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let w := heatSobolev μ Q s hs h
    let d := heatSobolevMap μ Q (s/2) (half_pos hs) (-heatGeneratorAt μ Q (s-s/2) h)
    ∃ (H : SobolevSpace μ Q) (τ : Measure X) (hτ : IsFiniteMeasure τ),
      letI := hτ;
      (SobolevSpace.toLp μ Q H =ᵐ[μ] localGamma μ Q w w) ∧
      IsMeasureLaplacianOn μ Q (ball p (2*r)) H (bochnerGramSource μ Q K w w d d τ.toSignedMeasure) := by
  intro μ Q w d
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨hLip,_⟩ := hX.kernelHeat_bounded_regularity hn p hk h A hA s hs
  have hw : SobolevSpace.toLp μ Q w =ᵐ[μ] kernelHeat μ Q hk s h := by
    simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 μ Q hk hs h).symm
  have hWA := (hX.bounded_heat_sobolev_data hn p h A hA hs).1
  have hd : IsWeakLaplacian μ Q w (SobolevSpace.toLp μ Q d) := heatTail_weak_laplacian μ Q s hs h
  obtain ⟨H,hH⟩ := hX.bounded_heat_gram hn p h A hA hs
  obtain ⟨_M,_hM,hM⟩ := hX.bounded_regular_bochner_mass hn hK p w d H hd
    (kernelHeat μ Q hk s h) hLip hw A hWA hH
  obtain ⟨τ,hτ,hτid,_hτmass⟩ := hM r hr
  let := hτ
  refine ⟨H,τ,hτ,hH,?_⟩
  apply bochner_measure_laplacian_of_source μ Q K w d H hH τ
  intro ψ v hv hvc hvs hψ
  exact hτid ψ v hv hvc (hvs.trans (ball_subset_ball (by linarith))) hψ

end RegularPointCoordinates

end

end OAI

import OAI.Geometry.RCD.Heat.CompactHeatStrongGradient
import OAI.Geometry.RCD.Sobolev.LocalGradientDifferenceRepresentative
import OAI.Geometry.RCD.Heat.ScaledHeatActionLimit

namespace OAI

/-! # Strong local gradient convergence to the constructed heat action

This uses the original convergent subsequence and arbitrary chosen local
Sobolev realizations. No further subsequence or gradient premise is needed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem CompactHeatConverges.strong_gradient (hK : K ≤ 0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S,ℝ)) (hF : ∀ k y, 0 < F k y)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (z : X) (ι : ℕ → ℕ) (H : ℝ → X → ℝ)
    (hconv : hX.CompactHeatConverges hn p ν F ε hε z ι H)
    {r δ t : ℝ} (hr : 0 < r) (hδ : 0 < δ) (ht : t ∈ Ioo δ 1)
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k)
      =ᵐ[(hausdorff n X).restrict (closedBall z r)]
        hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v
      =ᵐ[(hausdorff n X).restrict (closedBall z r)] H t)
    {R : ℝ} (hR : 0 ≤ R) (hdist : ∀ y:S, dist z y ≤ R)
    (φ : X → ℝ) {Lφ Bφ : ℝ≥0} (hφ : LipschitzWith Lφ φ)
    (hs : HasCompactSupport φ) (hBφ : ∀ x, |φ x| ≤ Bφ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hzero : ∀ x ∉ closedBall z r, φ x = 0) :
    Tendsto (fun k => weightedGamma (hausdorff n X) hX.quadratic (fun x => (φ x)^2)
      (u k-v) (u k-v)) atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨w,v',hw,hv',_hweak,_hcap,hlim⟩ := hX.compact_heat_strong_gradient hn p hK ν ρ hρ hρ0 hB hν
    (fun k => F (ι k)) (fun k => hF (ι k)) (fun k => ε (ι k)) (fun k => hε (ι k))
    (fun k => hε1 (ι k)) z hR hr hdist hδ ⟨ht.1.le,ht.2.le⟩ (H t)
    (hconv (2*r) (by positivity) δ hδ t ht) φ hφ hs hBφ hφ0 hzero
  have hwloc (k : ℕ) : SobolevSpace.toLp μ Q (w k)
      =ᵐ[μ.restrict (closedBall z r)] SobolevSpace.toLp μ Q (u k) := by
    filter_upwards [ae_restrict_of_ae (hw k),hu k,ae_restrict_mem measurableSet_closedBall]
      with x hx hy hmem
    rw [hx,radialCutoff_eq_one z hr (mem_closedBall'.mp hmem),one_mul,hy]
  have hvloc : SobolevSpace.toLp μ Q v' =ᵐ[μ.restrict (closedBall z r)] SobolevSpace.toLp μ Q v := by
    filter_upwards [ae_restrict_of_ae hv',hv,ae_restrict_mem measurableSet_closedBall]
      with x hx hy hmem
    rw [hx,radialCutoff_eq_one z hr (mem_closedBall'.mp hmem),one_mul,hy]
  apply hlim.congr'
  exact Eventually.of_forall fun k => weighted_gradient_difference_congr_on μ Q
    measurableSet_closedBall (hwloc k) hvloc (fun x => (φ x)^2)
      (fun x hx => by rw [hzero x hx]; norm_num)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

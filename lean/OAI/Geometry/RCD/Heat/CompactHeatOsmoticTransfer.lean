import OAI.Geometry.RCD.Heat.CompactHeatOsmoticVanishing
import OAI.Geometry.RCD.Sobolev.WeightedGammaLocality

namespace OAI

/-! # The osmotic energy limit for every local representative -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

namespace NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)



theorem local_osmotic_vanishes_of_rep (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R r δ : ℝ} (hR : 0 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ a : T, dist z a ≤ R) (hδ : 0 < δ)
    (φ : X → ℝ) (M : ℝ≥0) (hφ : LipschitzWith M φ) (hφs : HasCompactSupport φ)
    (hφ01 : ∀ x, φ x ∈ Icc (0:ℝ) 1) (hsupp : tsupport φ ⊆ closedBall z r)
    (η : ℕ → InteriorHeatTime δ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hη : ∀ k t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (η k t)
      =ᵐ[(hausdorff n X).restrict (tsupport φ)] D.osmoticPotential k t.val) :
    TendstoUniformly (fun k t => weightedGamma (hausdorff n X) hX.quadratic
      (fun x => φ x*D.interpolationDensity k t.val x) (η k t) (η k t)) (fun _ => 0) atTop := by
  obtain ⟨v,hv,hlim⟩ := D.local_osmotic_vanishes hK hε1 hε0 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hμ hν z hR hS hT hδ φ M hφ hφs hφ01 hsupp
  have he (k : ℕ) (t : InteriorHeatTime δ) :
      weightedGamma (hausdorff n X) hX.quadratic
        (fun x => φ x*D.interpolationDensity k t.val x) (η k t) (η k t) =
      weightedGamma (hausdorff n X) hX.quadratic
        (fun x => φ x*D.interpolationDensity k t.val x) (v k t) (v k t) := by
    have hsame := (hη k t).trans (hv k t).symm
    exact weightedGamma_congr_on (hausdorff n X) hX.quadratic (isClosed_tsupport φ).measurableSet
      hsame hsame _ (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx,zero_mul])
  have hfun : (fun k t => weightedGamma (hausdorff n X) hX.quadratic
      (fun x => φ x*D.interpolationDensity k t.val x) (η k t) (η k t)) =
      (fun k t => weightedGamma (hausdorff n X) hX.quadratic
        (fun x => φ x*D.interpolationDensity k t.val x) (v k t) (v k t)) := by
    funext k t
    exact he k t
  rw [hfun]
  exact hlim

end NoncollapsedRCD.CompactHeatScalingData
end RegularPointCoordinates

end

end OAI

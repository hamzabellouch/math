import OAI.Geometry.RCD.Sobolev.CutoffGaugeEnergy
import OAI.Geometry.RCD.Heat.ScaledHeatWeakEnergy
import OAI.Geometry.RCD.Heat.FixedGaugeTimePairing

namespace OAI

/-! # The exact weak energy equation for compact radial heat realizations -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology Interval
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_scaled_cutoff_energy
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S,ℝ)) (hF : ∀ a, 0 < F a) {ε : ℝ} (hε : 0 < ε)
    (z : X) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (u : Ioo δ 1 → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ t, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u t) =ᵐ[hausdorff n X]
      fun x => radialCutoff z r x*hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t x)
    (φ : SobolevSpace (hausdorff n X) hX.quadratic) (ξ : Lp ℝ 2 (hausdorff n X))
    (hξ : IsWeakLaplacian (hausdorff n X) hX.quadratic φ ξ)
    (hφs : ∀ᵐ x ∂hausdorff n X, x ∉ closedBall z r → SobolevSpace.toLp _ _ φ x = 0)
    (hξs : ∀ᵐ x ∂hausdorff n X, x ∉ closedBall z r → ξ x = 0)
    (Bφ : ℝ) (hBφ : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp _ _ φ x| ≤ Bφ)
    (θ θ' : ℝ → ℝ) (hθ : ContinuousOn θ (Icc δ 1)) (hθ' : ContinuousOn θ' (Icc δ 1))
    (hder : ∀ t ∈ Ioo δ 1, HasDerivAt θ (θ' t) t) (hθδ : θ δ = 0) (hθ1 : θ 1 = 0) :
    (∫ t : Ioo δ 1, θ t*weightedGamma (hausdorff n X) hX.quadratic
      (SobolevSpace.toLp _ _ φ) (u t) (u t) ∂volume.comap Subtype.val) =
      -2*(∫ t in Ioo δ 1, θ' t*∫ x in closedBall z r, SobolevSpace.toLp _ _ φ x*
        hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t x ∂hausdorff n X) -
      ε*(∫ t in Ioo δ 1, θ t*∫ x in closedBall z r, ξ x*
        hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t x ∂hausdorff n X) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let c := ε*Real.log (hX.compactHeatFactor hn p ν F ε hε z)
  let H := fun t x => ε*Real.log (∫ a, hX.canonicalHeatKernel hn p (ε*t/2) x a*F a ∂ν)
  obtain ⟨w,_q,hw,he⟩ := hX.compact_heat_scaled_weak_energy hn p
    ν ρ hρ hρ0 hB hν F hF hε z hr
  have hlocal (t : Ioo δ 1) : weightedGamma μ Q (SobolevSpace.toLp μ Q φ) (u t) (u t) =
      ∫ x in closedBall z r, SobolevSpace.toLp μ Q φ x*localGamma μ Q (w t) (w t) x ∂μ := by
    apply cutoff_gauge_weighted_energy μ Q z hr (u t) (w t) (H t) c _
      (hw t (hδ.trans t.property.1)).2 _ hφs
    apply (hu t).trans
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [hX.fixedGaugeScaledPotential_eq hn p ν F ε hε δ hδ z t.property.1.le x]
      rfl
  have hleft : (∫ t : Ioo δ 1, θ t*weightedGamma μ Q (SobolevSpace.toLp μ Q φ) (u t) (u t)
      ∂volume.comap Subtype.val) = ∫ t in Ioo δ 1, θ t*∫ x in closedBall z r,
        SobolevSpace.toLp μ Q φ x*localGamma μ Q (w t) (w t) x ∂μ := by
    simp_rw [hlocal]
    exact integral_subtype_comap measurableSet_Ioo (fun t => θ t*∫ x in closedBall z r,
      SobolevSpace.toLp μ Q φ x*localGamma μ Q (w t) (w t) x ∂μ)
  rw [hleft]
  have hh := he φ ξ hξ hφs hξs Bφ hBφ c δ 1 hδ hδ1 θ θ' hθ hθ' hder hθδ hθ1
  rw [hX.centered_interval_pairing_eq_fixed_gauge hn p ν F hε hδ hδ1 z
    (closedBall z r) (SobolevSpace.toLp μ Q φ) θ',
    hX.centered_interval_pairing_eq_fixed_gauge hn p ν F hε hδ hδ1 z (closedBall z r) ξ θ] at hh
  rw [intervalIntegral.integral_of_le hδ1,integral_Ioc_eq_integral_Ioo] at hh
  exact hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

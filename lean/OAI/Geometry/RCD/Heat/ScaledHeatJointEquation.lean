import OAI.Geometry.RCD.Heat.ScaledHeatTimePairing
import OAI.Geometry.RCD.Metric.ScaledCompactHamiltonJacobi

namespace OAI

/-! # The continuous time source equals the local Sobolev equation

The pointwise continuous source and all compact Sobolev realizations are
identified by uniqueness of the actual time derivative.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_scaled_joint_equation
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0 < F a) {ε : ℝ} (hε : 0 < ε) :
    let H := fun t x => ε * Real.log
      (∫ a, hX.canonicalHeatKernel hn p (ε*t/2) x a * F a ∂ν)
    ∃ D : ℝ → X → ℝ,
      ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ) ∧
      ContinuousOn (Function.uncurry D) (Ioi 0 ×ˢ univ) ∧
      (∀ t, 0 < t → ∀ x, HasDerivAt (fun s => H s x) (D t x) t) ∧
      ∀ t, 0 < t → ∀ Ω : Set X, IsCompact Ω →
        ∃ (w : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
          IsWeakLaplacian (hausdorff n X) hX.quadratic w q ∧
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic w
            =ᵐ[(hausdorff n X).restrict Ω] H t) ∧
          (D t =ᵐ[(hausdorff n X).restrict Ω] fun x =>
            ε/2*q x + localGamma (hausdorff n X) hX.quadratic w w x/2) := by
  intro H
  obtain ⟨D,hH,hD,hd⟩ := hX.compact_heat_scaled_time_data hn p ν ρ hρ hρ0 hB hν F hF hε
  refine ⟨D,hH,hD,hd,?_⟩
  intro t ht Ω hΩ
  obtain ⟨w,q,hq,hw,he⟩ := hX.compact_heat_factor_scaled_hamilton_jacobi hn p
    ν ρ hρ hρ0 hB hν F hF hε ht hΩ
  refine ⟨w,q,hq,hw,?_⟩
  filter_upwards [he] with x hx
  exact (hd t ht x).unique hx

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

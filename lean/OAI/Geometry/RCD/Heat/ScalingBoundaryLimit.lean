import OAI.Geometry.RCD.Heat.CompactScalingBoundary
import OAI.Geometry.RCD.Heat.ScaledHeatActionLimit
import OAI.Geometry.RCD.Sobolev.UniformCenteredConvergence

namespace OAI

/-! # Uniform limits of the actual normalized endpoint scaling factors -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_scaling_boundary_limit {S T : Set X} [CompactSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (F : ℕ → S → ℝ) (G : ℕ → C(T, ℝ))
    (hF : ∀ k a, 0 < F k a) (hG : ∀ k b, 0 < G k b)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (z : X) (ι : ℕ → ℕ)
    (H : ℝ → X → ℝ)
    (hconv : hX.CompactHeatConverges hn p ν G ε hε z ι H)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    (hr : ∀ k a, F k a*(∫ b, hX.canonicalHeatKernel hn p (ε k*t/2) a b*G k b ∂ν)=1)
    {R : ℝ} (hR : 0 ≤ R) (hdS : ∀ a : S, dist z a ≤ R) (a₀ : S) :
    TendstoUniformly (fun k (a : S) => ε (ι k)*(Real.log (F (ι k) a)-Real.log (F (ι k) a₀)))
      (fun a => H t a₀-H t a) atTop := by
  have hδ : 0 < t/2 := by linarith [ht.1]
  have hti : t ∈ Ioo (t/2) 1 := ⟨by linarith [ht.1],ht.2⟩
  let inc : S → closedBall z R := fun a => ⟨a,mem_closedBall.mpr (by
    simpa only [dist_comm] using hdS a)⟩
  have hh := (hconv R hR (t/2) hδ t hti).comp inc
  have hc := uniform_reverse_centered hh a₀
  apply (tendstoUniformly_congr (Eventually.of_forall (fun k => ?_))).mp hc
  funext a
  exact (hX.compact_scaling_centered_boundary hn p ν (F (ι k)) (G (ι k))
    (hF (ι k)) (hG (ι k)) (hε (ι k)) hδ hti.1.le (hr (ι k)) z a a₀).symm

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

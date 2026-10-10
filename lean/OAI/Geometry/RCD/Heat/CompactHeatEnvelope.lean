import OAI.Geometry.RCD.Heat.CompactHeatLaplaceLimit

namespace OAI

/-! # The actual action limit is the compact Hopf--Lax envelope

One maximum at the fixed reference time determines the gauge for every
interior time and point. The maximization is on the actual endpoint support.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem forward_envelope (a₀ : S) (hK : K ≤ 0) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hdS : ∀ a : S, dist p a ≤ R) :
    ∃ b ∈ μ.support,
      (∀ d ∈ μ.support, D.leftPotential a₀ d-dist p (d : X)^2/4 ≤
        D.leftPotential a₀ b-dist p (b : X)^2/4) ∧
      ∀ t ∈ Ioo (0:ℝ) 1, ∀ x : X, ∃ a ∈ μ.support,
        (∀ d ∈ μ.support, D.leftPotential a₀ d-dist x (d : X)^2/(2*t) ≤
          D.leftPotential a₀ a-dist x (a : X)^2/(2*t)) ∧
        D.forward.potential t x = (D.leftPotential a₀ a-dist x (a : X)^2/(2*t))-
          (D.leftPotential a₀ b-dist p (b : X)^2/4) := by
  obtain ⟨b,hb,hmaxb,hlimb⟩ := D.forward_laplace_limit a₀ hK hε0 hR hdS p
    (t := 2) (by norm_num)
  refine ⟨b,hb,by simpa only [show (2:ℝ)*2=4 by norm_num] using hmaxb,?_⟩
  intro t ht x
  obtain ⟨a,ha,hmaxa,hlima⟩ := D.forward_laplace_limit a₀ hK hε0 hR hdS x ht.1
  refine ⟨a,ha,hmaxa,?_⟩
  have hδ : 0 < t/2 := half_pos ht.1
  have hti : t ∈ Ioo (t/2) 1 := ⟨by linarith [ht.1],ht.2⟩
  have hx : x ∈ closedBall p (dist x p) := mem_closedBall.mpr le_rfl
  have hvalue := (D.forward_limit (dist x p) dist_nonneg (t/2) hδ t hti).tendsto_at ⟨x,hx⟩
  have he (k : ℕ) : hX.fixedGaugeScaledPotential hn p μ (D.left (D.index k))
      (ε (D.index k)) (hε (D.index k)) (t/2) hδ p t x =
      (ε (D.index k)*Real.log (hX.compactHeatFactor hn p μ (D.left (D.index k))
        (ε (D.index k)*t/2) (div_pos (mul_pos (hε (D.index k)) ht.1) (by norm_num)) x)-
        ε (D.index k)*Real.log (D.left (D.index k) a₀))-
      (ε (D.index k)*Real.log (hX.compactHeatFactor hn p μ (D.left (D.index k))
        (ε (D.index k)*2/2) (div_pos (mul_pos (hε (D.index k)) (by norm_num)) (by norm_num)) p)-
        ε (D.index k)*Real.log (D.left (D.index k) a₀)) := by
    rw [hX.fixedGaugeScaledPotential_eq hn p μ (D.left (D.index k))
      (ε (D.index k)) (hε (D.index k)) (t/2) hδ p hti.1.le x]
    simp only [scaledCompactHeatPotential,show ε (D.index k)*2/2=ε (D.index k) by ring]
    ring
  have hl := (hlima.sub hlimb).congr' (Eventually.of_forall fun k => (he k).symm)
  simpa only [show (2:ℝ)*2=4 by norm_num] using tendsto_nhds_unique hvalue hl

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI

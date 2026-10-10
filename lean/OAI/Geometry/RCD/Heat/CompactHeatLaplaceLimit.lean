import OAI.Geometry.RCD.Heat.CanonicalRowLogLimit
import OAI.Geometry.RCD.Heat.CompactHeatDualLimit
import OAI.Geometry.RCD.Heat.WeightedLaplaceLimit

namespace OAI

/-! # Actual compact heat factors converge to their variational envelopes -/

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

theorem forward_laplace_limit (a₀ : S) (hK : K ≤ 0) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hdS : ∀ a : S, dist p a ≤ R) (x : X) {t : ℝ} (ht : 0 < t) :
    ∃ a ∈ μ.support,
      (∀ b ∈ μ.support, D.leftPotential a₀ b-dist x (b : X)^2/(2*t) ≤
        D.leftPotential a₀ a-dist x (a : X)^2/(2*t)) ∧
      Tendsto (fun k => ε (D.index k)*Real.log (hX.compactHeatFactor hn p μ
        (D.left (D.index k)) (ε (D.index k)*t/2)
          (div_pos (mul_pos (hε (D.index k)) ht) (by norm_num)) x) -
        ε (D.index k)*Real.log (D.left (D.index k) a₀))
        atTop (𝓝 (D.leftPotential a₀ a-dist x (a : X)^2/(2*t))) := by
  let row : ℕ → C(S,ℝ) := fun k =>
    ⟨fun a => hX.canonicalHeatKernel hn p (ε (D.index k)*t/2) x a,
      (hX.canonicalHeatKernel_continuous_right hn p (ε (D.index k)*t/2)
        (div_pos (mul_pos (hε (D.index k)) ht) (by norm_num)) x).comp continuous_subtype_val⟩
  have hkpos (k : ℕ) (a : S) : 0 < row k a :=
    hX.canonicalHeatKernel_pos hn p _ (div_pos (mul_pos (hε (D.index k)) ht) (by norm_num)) x a
  have hrow := hX.canonicalHeatKernel_row_log_limit hn p hK (fun k => ε (D.index k))
    (fun k => hε (D.index k)) (hε0.comp D.strict.tendsto_atTop) hR hdS x ht
  obtain ⟨a,ha,hm,hl⟩ := weighted_laplace_limit μ row
    (fun k => D.left (D.index k)) (fun k => ε (D.index k)) a₀ (fun k => hε (D.index k))
    (hε0.comp D.strict.tendsto_atTop) hkpos (fun k => D.left_pos (D.index k))
    (fun a => -dist x (a : X)^2/(2*t)) (D.leftPotential a₀) (by fun_prop)
    (D.leftPotential a₀).continuous hrow (D.left_limit a₀)
  refine ⟨a,ha,?_,?_⟩
  · intro b hb
    have hh := hm b hb
    simp only [neg_div] at hh
    linarith
  · have he : -dist x (a : X)^2/(2*t)+D.leftPotential a₀ a =
        D.leftPotential a₀ a-dist x (a : X)^2/(2*t) := by ring
    rw [he] at hl
    exact hl

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI

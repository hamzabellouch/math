import OAI.Geometry.RCD.Heat.CompactHeatDualLimit

namespace OAI

/-! # The actual scaling densities and their uniform dual-slack limit -/

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

def density (k : ℕ) : C(S × T,ℝ) :=
  scaledContinuousKernel (D.kernel k) (D.left (D.index k)) (D.right (D.index k))

def slack (a₀ : S) (b₀ : T) (c : ℝ) : C(S × T,ℝ) :=
  ⟨fun q => D.leftPotential a₀ q.1-dist (q.1 : X) (q.2 : X)^2+D.rightPotential b₀ q.2+c,
    by fun_prop⟩

theorem density_pos (k : ℕ) (q : S × T) : 0 < D.density k q :=
  mul_pos (mul_pos (D.left_pos (D.index k) q.1) (D.kernel_pos k q)) (D.right_pos (D.index k) q.2)

theorem density_row (k : ℕ) (a : S) : (∫ b, D.density k (a,b) ∂ν)=1 := by
  rw [density,scaledContinuousKernel_row]
  exact D.row (D.index k) a

theorem density_col (k : ℕ) (b : T) : (∫ a, D.density k (a,b) ∂μ)=1 := by
  rw [density,scaledContinuousKernel_col]
  exact D.col (D.index k) b

def coupling (k : ℕ) : ProbabilityMeasure (S × T) :=
  ⟨continuousDensityCoupling μ ν (D.density k),
    continuousDensityCoupling_probability μ ν _ (fun q => (D.density_pos k q).le) (D.density_row k)⟩

theorem density_log_limit (a₀ : S) (b₀ : T) (c : ℝ) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R)
    (hc : Tendsto (fun k => ε (D.index k)*(Real.log (D.left (D.index k) a₀)+
      Real.log (D.right (D.index k) b₀))) atTop (𝓝 c)) :
    TendstoUniformly (fun k q => ε (D.index k)*Real.log (D.density k q))
      (D.slack a₀ b₀ c) atTop := by
  simpa only [density,slack,ContinuousMap.coe_mk,sub_eq_add_neg] using
    scaling_log_density_limit D.kernel (fun k => D.left (D.index k)) (fun k => D.right (D.index k))
      (fun k => ε (D.index k)) a₀ b₀ D.kernel_pos (fun k => D.left_pos (D.index k))
      (fun k => D.right_pos (D.index k)) (fun q => -dist (q.1 : X) (q.2 : X)^2)
      (D.leftPotential a₀) (D.rightPotential b₀) c
      (D.kernel_limit hK hε1 hε0 hR hdS hdT) (D.left_limit a₀) (D.right_limit b₀) hc

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI

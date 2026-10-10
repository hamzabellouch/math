import OAI.Geometry.RCD.Heat.CompactHeatScalingData
import OAI.Geometry.RCD.Heat.CanonicalCompactEndpoints
import OAI.Geometry.RCD.Coordinates.ScalingDualPotential
import OAI.Geometry.RCD.Metric.ScalingLogDensityLimit

namespace OAI

/-! # Dual slack of the actual compact heat scaling pair -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}

namespace CompactHeatScalingData
variable (D : hX.CompactHeatScalingData hn p μ ν ε hε)

def kernel (k : ℕ) : C(S × T,ℝ) := by
  let inc : S × T → X × X := fun q => (q.1.val,q.2.val)
  have hi : Continuous inc :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hk := hX.canonicalHeatKernel_continuous_joint hn p (ε (D.index k)/4)
    (div_pos (hε (D.index k)) (by norm_num))
  exact ⟨(fun q : X × X => hX.canonicalHeatKernel hn p (ε (D.index k)/4) q.1 q.2) ∘ inc,
    hk.comp hi⟩

def leftPotential (a₀ : S) : C(S,ℝ) :=
  ⟨fun a => D.backward.potential (1/2) a₀-D.backward.potential (1/2) a,
    continuous_const.sub ((D.backward.continuous_slice (by constructor <;> norm_num)).comp
      continuous_subtype_val)⟩

def rightPotential (b₀ : T) : C(T,ℝ) :=
  ⟨fun b => D.forward.potential (1/2) b₀-D.forward.potential (1/2) b,
    continuous_const.sub ((D.forward.continuous_slice (by constructor <;> norm_num)).comp
      continuous_subtype_val)⟩

theorem kernel_pos (k : ℕ) (q : S × T) : 0 < D.kernel k q := by
  change 0 < hX.canonicalHeatKernel hn p (ε (D.index k)/4) q.1 q.2
  exact hX.canonicalHeatKernel_pos hn p (ε (D.index k)/4)
    (div_pos (hε (D.index k)) (by norm_num)) q.1 q.2

theorem kernel_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R) :
    TendstoUniformly (fun k q => ε (D.index k)*Real.log (D.kernel k q))
      (fun q => -dist (q.1 : X) (q.2 : X)^2) atTop :=
  hX.canonicalHeatKernel_endpoint_log_limit hn p hK (fun k => ε (D.index k))
    (fun k => hε (D.index k)) (fun k => hε1 (D.index k))
    (hε0.comp D.strict.tendsto_atTop) hR hdS hdT

theorem dual_limit (a₀ : S) (b₀ : T) (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R) :
    ∃ c : ℝ,
      Tendsto (fun k => ε (D.index k)*(Real.log (D.left (D.index k) a₀)+
        Real.log (D.right (D.index k) b₀))) atTop (𝓝 c) ∧
      (∀ a b, b ∈ ν.support → D.leftPotential a₀ a-dist (a : X) (b : X)^2+
        D.rightPotential b₀ b+c ≤ 0) ∧
      ∀ a, ∃ b ∈ ν.support, D.leftPotential a₀ a-dist (a : X) (b : X)^2+
        D.rightPotential b₀ b+c = 0 := by
  simpa only [sub_eq_add_neg] using scaling_dual_potential ν D.kernel
    (fun k => D.left (D.index k)) (fun k => D.right (D.index k)) (fun k => ε (D.index k))
    a₀ b₀ (fun k => hε (D.index k)) (hε0.comp D.strict.tendsto_atTop)
    D.kernel_pos (fun k => D.left_pos (D.index k)) (fun k => D.right_pos (D.index k))
    (fun k => D.row (D.index k)) (fun q => -dist (q.1 : X) (q.2 : X)^2)
    (D.leftPotential a₀) (D.rightPotential b₀) (by fun_prop) (D.rightPotential b₀).continuous
    (D.kernel_limit hK hε1 hε0 hR hdS hdT) (D.left_limit a₀) (D.right_limit b₀)

end CompactHeatScalingData
end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

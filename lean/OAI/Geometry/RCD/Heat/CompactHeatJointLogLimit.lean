import OAI.Geometry.RCD.Heat.CompactHeatJointLaw
import OAI.Geometry.RCD.Heat.CanonicalFractionalKernelLog

namespace OAI

/-! # Exact logarithmic cost of the joint heat bridge

The limit retains both legs of the broken path. It is uniform on each
compact set of intermediate points, with the original endpoint potentials.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
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

def jointSlack (a₀ : S) (b₀ : T) (c : ℝ) (t : Ioo (0:ℝ) 1)
    (z : X × (S × T)) : ℝ :=
  D.leftPotential a₀ z.2.1-(dist z.1 z.2.1)^2/(t:ℝ)-
    (dist z.1 z.2.2)^2/(1-(t:ℝ))+D.rightPotential b₀ z.2.2+c

theorem jointSlack_continuous (a₀ : S) (b₀ : T) (c : ℝ) (t : Ioo (0:ℝ) 1) :
    Continuous (D.jointSlack a₀ b₀ c t) := by
  change Continuous (fun z : X × (S × T) =>
    D.leftPotential a₀ z.2.1-(dist z.1 z.2.1)^2/(t:ℝ)-
      (dist z.1 z.2.2)^2/(1-(t:ℝ))+D.rightPotential b₀ z.2.2+c)
  fun_prop

theorem joint_log_limit (a₀ : S) (b₀ : T) (c : ℝ) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hS : ∀ a:S, dist p a ≤ R) (hT : ∀ b:T, dist p b ≤ R)
    (hc : Tendsto (fun k => ε (D.index k)*(Real.log (D.left (D.index k) a₀)+
      Real.log (D.right (D.index k) b₀))) atTop (𝓝 c))
    (r : ℝ) (t : Ioo (0:ℝ) 1) :
    TendstoUniformly (fun k (z : closedBall p r × (S × T)) =>
      ε (D.index k)*Real.log (D.jointDensity (D.index k) t (z.1,z.2)))
      (fun z => D.jointSlack a₀ b₀ c t (z.1,z.2)) atTop := by
  let ε' k := ε (D.index k)
  have hε' : ∀ k, 0 < ε' k := fun k => hε (D.index k)
  have hε1' : ∀ k, ε' k ≤ 1 := fun k => hε1 (D.index k)
  have hε0' : Tendsto ε' atTop (𝓝 0) := hε0.comp D.strict.tendsto_atTop
  have hM : 0 ≤ max R r := hR.trans (le_max_left _ _)
  have hball (x : closedBall p r) : dist p x ≤ max R r := by
    have hx : dist p (x:X) ≤ r := by simpa only [mem_closedBall,dist_comm] using x.property
    exact hx.trans (le_max_right _ _)
  have hS' (a:S) : dist p a ≤ max R r := (hS a).trans (le_max_left _ _)
  have hT' (b:T) : dist p b ≤ max R r := (hT b).trans (le_max_left _ _)
  have hleftKernel := (hX.canonicalHeatKernel_fraction_log_limit hn p hK ε' hε' hε1' hε0'
    hM hball hS' t.property.1 t.property.2.le).comp
      (fun z : closedBall p r × (S × T) => (z.1,z.2.1))
  have hrightKernel := (hX.canonicalHeatKernel_fraction_log_limit hn p hK ε' hε' hε1' hε0'
    hM hball hT' (sub_pos.mpr t.property.2) (by linarith [t.property.1])).comp
      (fun z : closedBall p r × (S × T) => (z.1,z.2.2))
  have hleft := (D.left_limit a₀).comp (fun z : closedBall p r × (S × T) => z.2.1)
  have hright := (D.right_limit b₀).comp (fun z : closedBall p r × (S × T) => z.2.2)
  have hh := uniform_real_add (uniform_real_add (uniform_real_add
    (uniform_real_add hleft hleftKernel) hrightKernel) hright) hc.tendstoUniformly_const
  convert hh using 1
  · funext k z
    change ε' k*Real.log ((D.left (D.index k) z.2.1*
        hX.canonicalHeatKernel hn p (ε' k/4*t) z.1 z.2.1)*
      (hX.canonicalHeatKernel hn p (ε' k/4*(1-t)) z.1 z.2.2*D.right (D.index k) z.2.2)) = _
    have hp := hX.canonicalHeatKernel_pos hn p (ε' k/4*(t:ℝ))
      (mul_pos (div_pos (hε' k) (by norm_num)) t.property.1) (z.1:X) (z.2.1:X)
    have hq := hX.canonicalHeatKernel_pos hn p (ε' k/4*(1-(t:ℝ)))
      (mul_pos (div_pos (hε' k) (by norm_num)) (sub_pos.mpr t.property.2)) (z.1:X) (z.2.2:X)
    rw [Real.log_mul (mul_pos (D.left_pos (D.index k) z.2.1) hp).ne'
        (mul_pos hq (D.right_pos (D.index k) z.2.2)).ne',
      Real.log_mul (D.left_pos (D.index k) z.2.1).ne' hp.ne',
      Real.log_mul hq.ne' (D.right_pos (D.index k) z.2.2).ne']
    dsimp only [Function.comp_apply,ε']
    ring
  · funext z
    dsimp only [Function.comp_apply,jointSlack,leftPotential,rightPotential,ContinuousMap.coe_mk]
    ring

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI

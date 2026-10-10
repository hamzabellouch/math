import OAI.Geometry.RCD.Heat.CompactHeatJointLogLimit
import OAI.Geometry.RCD.Transport.BrokenGeodesicCost

namespace OAI

/-! # The zero joint-slack set consists of geodesic triples -/

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

theorem jointSlack_nonpos (a₀ : S) (b₀ : T) (c : ℝ) (t : Ioo (0:ℝ) 1)
    (x : X) (a : S) (b : T) (hdual : D.slack a₀ b₀ c (a,b) ≤ 0) :
    D.jointSlack a₀ b₀ c t (x,(a,b)) ≤ 0 := by
  have htriangle : dist (a:X) (b:X) ≤ dist x (a:X)+dist x (b:X) := by
    simpa only [dist_comm (a:X) x] using dist_triangle (a:X) x (b:X)
  have hh := two_leg_cost_nonneg (dist_nonneg (x := x) (y := (a:X)))
    (dist_nonneg (x := x) (y := (b:X))) (dist_nonneg (x := (a:X)) (y := (b:X)))
    htriangle t.property.1 t.property.2
  dsimp only [jointSlack,slack,ContinuousMap.coe_mk] at hdual ⊢
  linarith only [hh,hdual]

theorem jointSlack_zero_geodesic (a₀ : S) (b₀ : T) (c : ℝ) (t : Ioo (0:ℝ) 1)
    (x : X) (a : S) (b : T) (hdual : D.slack a₀ b₀ c (a,b) ≤ 0)
    (hzero : D.jointSlack a₀ b₀ c t (x,(a,b)) = 0) :
    dist x (a:X)=(t:ℝ)*dist (a:X) (b:X) ∧
      dist x (b:X)=(1-(t:ℝ))*dist (a:X) (b:X) ∧ D.slack a₀ b₀ c (a,b)=0 := by
  have htriangle : dist (a:X) (b:X) ≤ dist x (a:X)+dist x (b:X) := by
    simpa only [dist_comm (a:X) x] using dist_triangle (a:X) x (b:X)
  have hcost := two_leg_cost_nonneg (dist_nonneg (x := x) (y := (a:X)))
    (dist_nonneg (x := x) (y := (b:X))) (dist_nonneg (x := (a:X)) (y := (b:X)))
    htriangle t.property.1 t.property.2
  have he : (dist x (a:X))^2/(t:ℝ)+(dist x (b:X))^2/(1-(t:ℝ))-(dist (a:X) (b:X))^2=0 := by
    dsimp only [jointSlack,slack,ContinuousMap.coe_mk] at hdual hzero
    linarith only [hdual,hzero,hcost]
  obtain ⟨ha,hb⟩ := two_leg_cost_zero (dist_nonneg (x := x) (y := (a:X)))
    (dist_nonneg (x := x) (y := (b:X))) (dist_nonneg (x := (a:X)) (y := (b:X)))
    htriangle t.property.1 t.property.2 he
  refine ⟨ha,hb,?_⟩
  dsimp only [jointSlack,slack,ContinuousMap.coe_mk] at hzero ⊢
  linarith only [hzero,he]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI

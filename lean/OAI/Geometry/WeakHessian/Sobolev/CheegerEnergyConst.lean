import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ConstLp
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeat
import OAI.Geometry.WeakHessian.HeatFlow.ResolventEnergy

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X} [IsFiniteMeasure m]
lemma cheegerEnergy_const (c : ℝ) : cheegerEnergy m (fun _ : X => c) = 0 := by
  have H := cheegerEnergy_le_liminf (memLp_const (μ := m) (p := 2) c)
    (fs := fun _ : ℕ => fun _ : X => c) (fun _ => ⟨⟨0,LipschitzWith.const c⟩,memLp_const c⟩)
    (by simp)
  have hs : ∀ x : X, localSlope (fun _ : X => c) x = 0 := by
    intro x
    exact le_antisymm (by simpa using localSlope_le_lipschitz (LipschitzWith.const c) x) bot_le
  have H0 : cheegerEnergy m (fun _ : X => c) ≤ 0 := by simpa [hs] using H
  exact le_antisymm H0 bot_le

lemma cheegerHeat_const (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    cheegerHeat h t (constLp c) = constLp c := by
  apply (cheeger_closedQuadraticEnergy h).heat_fixed_of_energy_zero m _ ht
  rw [cheegerEnergy_congr_ae (constLp_coe c), cheegerEnergy_const]

omit [MetricSpace X] in
lemma integral_eq_inner_const (u : Lp ℝ 2 m) : (∫ x, u x ∂m) = ⟪constLp 1,u⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [constLp_coe (m := m) 1] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_one]

lemma cheegerHeat_mass (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t) (u : Lp ℝ 2 m) :
    (∫ x, cheegerHeat h t u x ∂m) = ∫ x, u x ∂m := by
  rw [integral_eq_inner_const, integral_eq_inner_const]
  have H := cheegerHeat_symmetric h t (constLp 1) u
  change ⟪cheegerHeat h t (constLp 1),u⟫_ℝ = ⟪constLp 1,cheegerHeat h t u⟫_ℝ at H
  rw [cheegerHeat_const h ht] at H
  exact H.symm

omit [IsFiniteMeasure m] in
lemma cheegerHeat_energy_le (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t) (u : Lp ℝ 2 m) :
    cheegerEnergy m (cheegerHeat h t u : X → ℝ) ≤ cheegerEnergy m (u : X → ℝ) :=
  (cheeger_closedQuadraticEnergy h).heat_energy_le m ht u

end WeakHessian

end
end InlinedFile0

end OAI

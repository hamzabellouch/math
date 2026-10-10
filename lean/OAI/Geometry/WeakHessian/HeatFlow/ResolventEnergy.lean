import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.ScaledResolventCfc

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

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.resolvent_energy_le (u : E) : Q (hQ.resolvent u) ≤ Q u := by
  have H := hQ.resolvent_minimizes u u
  have hle : Q (hQ.resolvent u) ≤ proximalFunctional Q u (hQ.resolvent u) := le_add_right le_rfl
  simpa only [proximalFunctional, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div, ENNReal.ofReal_zero, add_zero] using hle.trans H

lemma ClosedQuadraticEnergy.resolvent_fixed_of_energy_zero {u : E} (hu : Q u = 0) :
    hQ.resolvent u = u := by
  have H := hQ.resolvent_minimizes u u
  have hle : ENNReal.ofReal (‖hQ.resolvent u-u‖^2/2) ≤
      proximalFunctional Q u (hQ.resolvent u) := le_add_left le_rfl
  have hz : ENNReal.ofReal (‖hQ.resolvent u-u‖^2/2) ≤ 0 := by
    simpa only [proximalFunctional, hu, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, ENNReal.ofReal_zero, add_zero] using hle.trans H
  have hh := ENNReal.ofReal_eq_zero.mp (le_antisymm hz bot_le)
  have hn : ‖hQ.resolvent u-u‖ = 0 := by nlinarith [norm_nonneg (hQ.resolvent u-u)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.heat_energy_le {t : ℝ} (ht : 0 ≤ t) (u : Lp ℝ 2 m) :
    Q (realHeat m hQ.resolventLinear t u) ≤ Q u := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [realHeat_zero m hQ.resolvent_positive]
    rfl
  have hstep {s : ℝ} (hs : 0 < s) (v : Lp ℝ 2 m) :
      Q ((hQ.scale hs).resolventLinear v) ≤ Q v := by
    apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top).mp
    exact (hQ.scale hs).resolvent_energy_le v
  have hp {s : ℝ} (hs : 0 < s) (n : ℕ) :
      Q ((((hQ.scale hs).resolventLinear)^n) u) ≤ Q u := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      simpa only [pow_succ', mul_apply_eq_comp] using
        (hstep hs ((((hQ.scale hs).resolventLinear)^n) u)).trans ih
  exact (hQ.lowerSemicontinuous.isClosed_preimage (Q u)).mem_of_tendsto
    (hQ.euler_tendsto_heat m ht u) (Eventually.of_forall fun n => hp (by positivity) (2^n))

lemma ClosedQuadraticEnergy.heat_fixed_of_energy_zero {u : Lp ℝ 2 m} (hu : Q u = 0)
    {t : ℝ} (ht : 0 ≤ t) : realHeat m hQ.resolventLinear t u = u := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [realHeat_zero m hQ.resolvent_positive]
    rfl
  have hs {s : ℝ} (hs : 0 < s) : (hQ.scale hs).resolventLinear u = u := by
    apply (hQ.scale hs).resolvent_fixed_of_energy_zero
    rw [hu, mul_zero]
  have hp {s : ℝ} (hs' : 0 < s) (n : ℕ) :
      (((hQ.scale hs').resolventLinear)^n) u = u := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ', mul_apply_eq_comp, ih] using hs hs'
  apply tendsto_nhds_unique (hQ.euler_tendsto_heat m ht u)
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u)).congr'
    (Eventually.of_forall fun n => (hp (by positivity : 0 < t/(2:ℝ)^n) (2^n)).symm)

end WeakHessianFunctional

end
end InlinedFile0

end OAI

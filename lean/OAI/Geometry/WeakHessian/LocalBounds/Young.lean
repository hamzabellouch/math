import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergySlope
import OAI.Geometry.WeakHessian.LocalBounds.RelaxedProx

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma RelaxedProx.young {u v D q : Lp ℝ 2 m} {t α c : ℝ} (h : RelaxedProx u t v D)
    (hq : cheegerEnergy m (q : X → ℝ) < ∞) (hα : 0 < α) :
    -α*(cheegerEnergy m (q : X → ℝ)).toReal + ⟪q,c • (u-v)⟫_ℝ ≤
      c^2/α*(t^2*‖D‖)^2/2 := by
  obtain ⟨E,hE,_hmin,he⟩ := exists_relaxedGradient_energy_eq hq
  rw [he,ENNReal.toReal_ofReal (by positivity : 0 ≤ ‖E‖^2/2),real_inner_smul_right,
    real_inner_comm (u-v) q]
  have HB : c*⟪u-v,q⟫_ℝ ≤ |c| * (t^2*‖D‖)*‖E‖ := by
    calc
      _ ≤ |c*⟪u-v,q⟫_ℝ| := le_abs_self _
      _ = |c| * |⟪u-v,q⟫_ℝ| := abs_mul _ _
      _ ≤ |c| * (t^2*‖D‖*‖E‖) := mul_le_mul_of_nonneg_left (h.dual hE) (abs_nonneg c)
      _ = _ := by ring
  have HP := sq_nonneg (|c| * (t^2*‖D‖)-α*‖E‖)
  have HE : (|c| * (t^2*‖D‖))^2 = c^2*(t^2*‖D‖)^2 := by rw [mul_pow,sq_abs]
  have HC := mul_le_mul_of_nonneg_left HB hα.le
  have hr : c^2/α*(t^2*‖D‖)^2/2 = (c^2*(t^2*‖D‖)^2)/(2*α) := by ring
  rw [hr]
  apply (le_div_iff₀ (by positivity : 0 < 2*α)).mpr
  nlinarith
end WeakHessian

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

end

end OAI

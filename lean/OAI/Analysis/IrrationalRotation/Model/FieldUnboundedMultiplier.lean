import OAI.Analysis.IrrationalRotation.Model.WeightedShift
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.LinearPMap

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

abbrev FieldHilbert := Lp Hilbert 2 μ

def fieldMultiplierGraph (h : X → ℤ → ℂ) :
    Submodule ℂ (FieldHilbert μ × FieldHilbert μ) where
  carrier := {p | ∀ᵐ x ∂μ, ∀ k, p.2 x k = h x k * p.1 x k}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero Hilbert 2 μ] with x hx
    intro k
    simp only [Prod.fst_zero, Prod.snd_zero, hx, Pi.zero_apply, lp.coeFn_zero, mul_zero]
  add_mem' := by
    intro p q hp hq
    filter_upwards [hp, hq, Lp.coeFn_add p.1 q.1, Lp.coeFn_add p.2 q.2]
      with x hp hq hfst hsnd
    intro k
    change (p.2 + q.2) x k = h x k * (p.1 + q.1) x k
    rw [hsnd, hfst]
    change p.2 x k + q.2 x k = h x k * (p.1 x k + q.1 x k)
    rw [hp, hq, mul_add]
  smul_mem' := by
    intro c p hp
    filter_upwards [hp, Lp.coeFn_smul c p.1, Lp.coeFn_smul c p.2]
      with x hp hfst hsnd
    intro k
    change (c • p.2) x k = h x k * (c • p.1) x k
    rw [hsnd, hfst]
    change c * p.2 x k = h x k * (c * p.1 x k)
    rw [hp, mul_left_comm]

def fieldUnboundedMultiplier (h : X → ℤ → ℂ) :
    FieldHilbert μ →ₗ.[ℂ] FieldHilbert μ :=
  (fieldMultiplierGraph μ h).toLinearPMap

end Invariant233.WeightedShift

end

end OAI

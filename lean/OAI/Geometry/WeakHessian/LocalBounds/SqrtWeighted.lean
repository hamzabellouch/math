import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma sqrt_le_weighted {u V : ℝ} (hu : 0 ≤ u) :
    Real.sqrt u ≤ (u*Real.exp (V/2)+Real.exp (-(V/2)))/2 := by
  have hd := Real.exp_pos (-(V/2))
  have heer : (u*Real.exp (V/2))*Real.exp (-(V/2)) = u := by
    rw [mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  apply (mul_le_mul_iff_left₀ hd).mp
  nlinarith [sq_nonneg (Real.sqrt u-Real.exp (-(V/2))),Real.sq_sqrt hu]

lemma integrable_sqrt_weighted {u V : X → ℝ}
    (hu : AEStronglyMeasurable u m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hw : Integrable (fun x => Real.exp (-(V x/2))) m) :
    Integrable (fun x => Real.sqrt (u x)) m ∧
      (∫ x,Real.sqrt (u x) ∂m) ≤
        (‖hU.toLp (fun x => u x*Real.exp (V x))‖*‖hD.toLp (fun x => Real.exp (-(V x/2)))‖+
          ∫ x,Real.exp (-(V x/2)) ∂m)/2 := by
  have hg : MemLp (fun x => Real.exp (V x/2)*Real.exp (-V x)) 2 m := by
    have he : (fun x => Real.exp (V x/2)*Real.exp (-V x)) = (fun x => Real.exp (-(V x/2))) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [he]
  have H := weighted_pairing hU hg
  have hnorm : ‖hg.toLp (fun x => Real.exp (V x/2)*Real.exp (-V x))‖ =
      ‖hD.toLp (fun x => Real.exp (-(V x/2)))‖ := by
    congr 1
    apply Lp.ext
    filter_upwards [hg.coeFn_toLp,hD.coeFn_toLp] with x hx hy
    rw [hx,hy,← Real.exp_add]
    congr 1
    ring
  rw [hnorm] at H
  have hi : Integrable (fun x => Real.sqrt (u x)) m := by
    apply ((H.1.add hw).div_const 2).mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hu)
    filter_upwards [hun] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Pi.add_apply] using! sqrt_le_weighted (V := V x) hx
  refine ⟨hi,?_⟩
  calc
    (∫ x,Real.sqrt (u x) ∂m) ≤ ∫ x,(u x*Real.exp (V x/2)+Real.exp (-(V x/2)))/2 ∂m :=
      integral_mono_ae hi ((H.1.add hw).div_const 2) (hun.mono fun x hx => sqrt_le_weighted hx)
    _ = ((∫ x,u x*Real.exp (V x/2) ∂m)+(∫ x,Real.exp (-(V x/2)) ∂m))/2 := by
      rw [integral_div,integral_add H.1 hw]
    _ ≤ _ := by
      have HH := (le_abs_self (∫ x,u x*Real.exp (V x/2) ∂m)).trans H.2
      linarith
end WeakHessian

end
end InlinedFile0

end OAI

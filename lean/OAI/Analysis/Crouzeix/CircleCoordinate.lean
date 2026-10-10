import Mathlib
import OAI.Analysis.Crouzeix.BoundaryOperators

namespace OAI

/-! Circle Coordinate. -/

noncomputable section

open Set Metric Filter Topology Complex MeasureTheory

namespace CrouzeixHilbert.Boundary

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def circleCoordinate : C(CircleSpace, ℂ) := fourier 1

@[simp] lemma norm_circleCoordinate (t : CircleSpace) : ‖circleCoordinate t‖ = 1 := by
  rw [circleCoordinate, fourier_apply, Circle.norm_coe]

lemma circleCoordinate_ne_zero (t : CircleSpace) : circleCoordinate t ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_circleCoordinate]; exact one_ne_zero)

lemma circleCoordinate_injective : Function.Injective circleCoordinate := by
  intro x y h
  apply AddCircle.injective_toCircle (T := 1) one_ne_zero
  apply Subtype.coe_injective
  simpa only [circleCoordinate, fourier_one] using h

@[simp] lemma circleCoordinate_neg (t : CircleSpace) :
    circleCoordinate (-t) = (circleCoordinate t)⁻¹ := by
  simp only [circleCoordinate, fourier_one, AddCircle.toCircle_neg, Circle.coe_inv]

lemma circleCoordinate_coe (x : ℝ) :
    circleCoordinate (x : CircleSpace) = circleMap 0 1 (2 * Real.pi * x) := by
  rw [circleCoordinate, fourier_coe_apply]
  simp only [Int.cast_one, mul_one, ofReal_one, div_one, circleMap, ofReal_mul,
    ofReal_ofNat, zero_add, one_mul]
  congr 1
  ring

lemma integral_circleCoordinate_eq_circleAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ t, f (circleCoordinate t) ∂circleMeasure) = Real.circleAverage f 0 1 := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add, circleCoordinate_coe]
  rw [intervalIntegral.integral_comp_mul_left (fun θ => f (circleMap 0 1 θ)) (ne_of_gt Real.two_pi_pos)]
  simp only [mul_zero, mul_one, Real.circleAverage]

lemma integral_inverse_circleCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ t, f (circleCoordinate t)⁻¹ ∂circleMeasure) = Real.circleAverage f 0 1 := by
  simp_rw [← circleCoordinate_neg]
  rw [integral_neg_eq_self (fun t => f (circleCoordinate t)) circleMeasure, integral_circleCoordinate_eq_circleAverage]

lemma integral_holomorphic_circleCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    (∫ t, f (circleCoordinate t) ∂circleMeasure) = f 0 := by
  rw [integral_circleCoordinate_eq_circleAverage]
  apply DiffContOnCl.circleAverage
  apply DifferentiableOn.diffContOnCl
  simpa only [abs_one, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)] using hf

lemma integral_holomorphic_inverse_circleCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    (∫ t, f (circleCoordinate t)⁻¹ ∂circleMeasure) = f 0 := by
  simp_rw [← circleCoordinate_neg]
  rw [integral_neg_eq_self (fun t => f (circleCoordinate t)) circleMeasure, integral_holomorphic_circleCoordinate hf]

end CrouzeixHilbert.Boundary

end

end OAI

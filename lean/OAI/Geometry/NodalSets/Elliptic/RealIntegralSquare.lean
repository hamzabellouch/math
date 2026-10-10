import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
noncomputable section

lemma real_integral_square_le {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (hm : 0 < mu.real univ) (f : X → ℝ) (hf : Integrable f mu)
    (hf2 : Integrable (fun x ↦ f x^2) mu) :
    (∫ x, f x ∂mu)^2 ≤ mu.real univ*(∫ x, f x^2 ∂mu) := by
  let m := mu.real univ
  let I := ∫ x, f x ∂mu
  let q := I/m
  have hq : m*q=I := mul_div_cancel₀ I hm.ne'
  have he : (fun x ↦ (f x-q)^2) = fun x ↦ (f x^2-(2*q)*f x)+q^2 := by
    funext x
    ring
  have hnonneg : 0 ≤ ∫ x, (f x-q)^2 ∂mu := integral_nonneg (fun x ↦ sq_nonneg (f x-q))
  have hsub : Integrable (fun x ↦ f x^2-(2*q)*f x) mu := hf2.sub (hf.const_mul _)
  rw [he,integral_add hsub (integrable_const _),
    integral_sub hf2 (hf.const_mul _),integral_const_mul,integral_const] at hnonneg
  change 0 ≤ (∫ x, f x^2 ∂mu)-(2*q)*I+m*q^2 at hnonneg
  have hmul := mul_nonneg hm.le hnonneg
  have hpoly : m*((∫ x, f x^2 ∂mu)-(2*q)*I+m*q^2) =
      m*(∫ x, f x^2 ∂mu)-I^2 := by
    calc
      _ = m*(∫ x, f x^2 ∂mu)-2*(m*q)*I+(m*q)^2 := by ring
      _ = _ := by rw [hq]; ring
  rw [hpoly] at hmul
  exact sub_nonneg.mp hmul

end
end Yau.Geometry

end OAI

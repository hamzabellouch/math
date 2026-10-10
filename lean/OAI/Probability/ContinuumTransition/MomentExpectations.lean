import OAI.Probability.ContinuumTransition.MomentBounds

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem exp_exterior_field_le {ι : Type u_1} [Fintype ι] (J n : ι → ℝ)
    {A β : ℝ} (hA : 0 < A) (hβ : 0 ≤ β) (hJ : ∀ j, 0 ≤ J j)
    (hrow : ∑ j, J j ≤ A/8) :
    Real.exp (β*(∑ j, J j*n j)^2/A) ≤
      1+∑ j, J j/A*Real.exp (β*A/8*(n j)^2) := by
  have hs := weighted_field_sq J n hJ hrow
  have hfield : β*(∑ j, J j*n j)^2/A ≤ ∑ j, (J j/A)*(β*A/8*(n j)^2) := by
    calc
      _ = β/A*(∑ j, J j*n j)^2 := by ring
      _ ≤ β/A*(A/8*∑ j, J j*(n j)^2) :=
        mul_le_mul_of_nonneg_left hs (div_nonneg hβ hA.le)
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        field_simp
  have hweights : ∑ j, J j/A ≤ 1 := by
    rw [← Finset.sum_div]
    apply (div_le_one hA).2
    linarith
  have hj := convexOn_exp.map_add_sum_le (t := Finset.univ)
    (w := fun j => J j/A) (p := fun j => β*A/8*(n j)^2)
    (v := 1-∑ j, J j/A) (q := 0)
    (fun j _ => div_nonneg (hJ j) hA.le) (by ring)
    (fun _ _ => mem_univ _) (sub_nonneg.mpr hweights) (mem_univ _)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hj
  have hw0 : 0 ≤ ∑ j, J j/A := Finset.sum_nonneg (fun j _ => div_nonneg (hJ j) hA.le)
  exact ((Real.exp_le_exp.mpr hfield).trans hj).trans (by linarith only [hw0])

end ContinuumTemperature
end

end OAI

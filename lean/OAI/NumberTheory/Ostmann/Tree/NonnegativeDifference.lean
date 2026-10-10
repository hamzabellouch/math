import OAI.NumberTheory.Ostmann.Tree.CrossMajorantBounds

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

theorem unitMean_nonneg (f : ZMod p → ℝ) (hf : ∀ x,0≤f x) : 0≤unitMean f := by
  unfold unitMean
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun x _ => hf x))

theorem unitMean_sum {I : Type*} (S : Finset I) (f : I → ZMod p → ℝ) :
    unitMean (fun y => ∑ i ∈ S,f i y)=∑ i ∈ S,unitMean (f i) := by
  unfold unitMean
  rw [Finset.sum_comm,Finset.mul_sum]

def nonnegativeDifference (A B : ZMod p → ℝ) (y : ZMod p) : ℝ :=
  (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*∑ d : ZMod p,A d*B (d-y)

theorem nonnegativeDifference_nonneg (A B : ZMod p → ℝ)
    (hA : ∀ d,0≤A d) (hB : ∀ d,0≤B d) (y : ZMod p) :
    0≤nonnegativeDifference A B y := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun d _ => mul_nonneg (hA d) (hB _)))

theorem nonnegativeDifference_mean (A B : ZMod p → ℝ)
    (hA : ∀ d,0≤A d) (hB : ∀ d,0≤B d) :
    unitMean (nonnegativeDifference A B) ≤
      (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*((∑ d,A d)*(∑ e,B e)) := by
  unfold unitMean nonnegativeDifference
  rw [← Finset.mul_sum]
  calc
    _ = (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*(∑ y : (ZMod p)ˣ,∑ d : ZMod p,A d*B (d-y)) := by ring
    _ ≤ (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*(∑ y : ZMod p,∑ d : ZMod p,A d*B (d-y)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_units_le (fun y : ZMod p => ∑ d : ZMod p,A d*B (d-y))
        (fun y => Finset.sum_nonneg (fun d _ => mul_nonneg (hA d) (hB _)))
    _ = _ := by rw [sum_difference_products]

end
end Ostmann.FiniteField

end OAI

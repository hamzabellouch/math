import OAI.Combinatorics.SharpThreshold.FourierBasis

namespace OAI

universe u

noncomputable section

open scoped BigOperators
open Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

/-- Separate the new coordinate from the product Bernoulli weight. -/
theorem weight_option (p : ℝ) (x : Option ι → Bool) :
    weight p x = scalarWeight p (x none) * weight p (fun i => x (some i)) := by
  simp only [weight, Fintype.prod_option]

@[simp] theorem weight_option_elim (p : ℝ) (b : Bool) (x : ι → Bool) :
    weight p ((fun i : Option ι => Option.elim i b x)) = scalarWeight p b * weight p x := by
  rw [weight_option]
  rfl

/-- Exact expectation splitting at the distinguished `none` coordinate.
This identity is polynomial and requires no restriction on the bias. -/
theorem weighted_sum_option (p : ℝ) (g : (Option ι → Bool) → ℝ) :
    (∑ x, weight p x * g x) =
      (1 - p) * (∑ y, weight p y * g ((fun i : Option ι => Option.elim i false y))) +
        p * (∑ y, weight p y * g ((fun i : Option ι => Option.elim i true y))) := by
  let e : (Option ι → Bool) ≃ Bool × (ι → Bool) := Equiv.piOptionEquivProd
  rw [← e.symm.sum_comp (fun x => weight p x * g x), Fintype.sum_prod_type,
    Fintype.sum_bool]
  have he (b : Bool) (y : ι → Bool) : e.symm (b, y) = (fun i : Option ι => Option.elim i b y) := by
    funext i
    cases i <;> rfl
  simp_rw [he, weight_option_elim, scalarWeight_true, scalarWeight_false,
    mul_assoc, ← Finset.mul_sum]
  ring

end Problem313.BiasedFourier

end

end OAI

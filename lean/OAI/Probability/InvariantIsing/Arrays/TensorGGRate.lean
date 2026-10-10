import OAI.Probability.InvariantIsing.Arrays.PerturbationMinimumRates
import OAI.Probability.InvariantIsing.Arrays.MonomialEnumeration

namespace OAI

/-! The complete tensor GG rate tends to zero for every fixed monomial. -/

noncomputable section

open IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

def tensorContactGGRate (N j m : ℕ) (L B : ℝ) : ℝ :=
  contactGGRate N j L B + 2 * B * (∑ a, (enumeratedSpectralDegree m j a : ℝ)) * diagonalContactRate N L

lemma tensorContactGGRate_tendsto (j m : ℕ) (L B : ℝ) :
    Tendsto (fun N => tensorContactGGRate N j m L B) atTop (nhds 0) := by
  have h := (contactGGRate_tendsto j L B).add
    ((diagonalContactRate_tendsto L).const_mul (2 * B * ∑ a, (enumeratedSpectralDegree m j a : ℝ)))
  simpa only [tensorContactGGRate, mul_zero, add_zero] using h

end InvariantIsing

end

end OAI

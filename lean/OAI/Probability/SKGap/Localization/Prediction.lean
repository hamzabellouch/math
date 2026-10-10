import Mathlib
import OAI.Probability.SKGap.Matrix.PolynomialCoeListSum

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open PowerSeries
variable {ι : Type*} [Fintype ι]

theorem literalSeries_coeff_eq_zero (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι))
    (hI : inverseCount F≤1) (i : ι) (n : ℕ) (hn : ordinaryCount F<n) :
    PowerSeries.coeff n (literalSeries j a F i)=0 := by
  rw [literalSeries_eq_wordPredictionPolynomial j a F hI i,Polynomial.coeff_coe]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((wordPredictionPolynomial_spec j a F i).1.trans_lt hn)

def sourcePrediction (j : ℝ) (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ :=
  Polynomial.eval z (PowerSeries.trunc (ordinaryCount F+1) (literalSeries j a F i))

theorem sourcePrediction_eq_wordPrediction (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F : List (WordLetter ι)) (hI : inverseCount F≤1) (i : ι) :
    sourcePrediction j a z F i=wordPrediction j a z F i := by
  unfold sourcePrediction
  rw [literalSeries_eq_wordPredictionPolynomial j a F hI i,
    PowerSeries.trunc_coe_eq_self (Nat.lt_succ_of_le (wordPredictionPolynomial_spec j a F i).1)]
  exact (wordPredictionPolynomial_spec j a F i).2 z
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

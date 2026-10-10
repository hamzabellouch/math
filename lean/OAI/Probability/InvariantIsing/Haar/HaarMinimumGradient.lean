import OAI.Probability.InvariantIsing.Haar.HaarPolynomialMinimum
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialGamma

namespace OAI

/-! Every coordinate-plane derivative vanishes at a global polynomial minimum. -/
noncomputable section
open Matrix MvPolynomial Filter
open scoped Topology BigOperators
namespace InvariantIsing

lemma haarPolynomialDerivation_zero_at_min {N : ℕ}
    (p : MatrixPolynomial N) (U : SpecialOrthogonal N)
    (hmin : ∀ V : SpecialOrthogonal N, haarPolynomialValue p U ≤ haarPolynomialValue p V)
    (i j : Fin N) :
    haarPolynomialValue (matrixPolynomialDerivation (planeGenerator i j) p) U = 0 := by
  have hm : IsLocalMin (fun t => haarPolynomialValue p (specialPlaneRotation i j t*U)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [specialPlaneRotation_zero,one_mul] using hmin (specialPlaneRotation i j t*U)
  have hd := hasDerivAt_specialPlaneRotation_polynomial p i j U 0
  simp only [specialPlaneRotation_zero,one_mul] at hd
  exact hm.hasDerivAt_eq_zero hd

lemma haarPolynomialGamma_zero_at_min {N : ℕ}
    (p q : MatrixPolynomial N) (U : SpecialOrthogonal N)
    (hmin : ∀ V : SpecialOrthogonal N, haarPolynomialValue p U ≤ haarPolynomialValue p V) :
    haarPolynomialValue (haarPolynomialGamma q p) U = 0 := by
  change matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) _ = 0
  simp only [haarPolynomialGamma,map_sum,map_mul]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  change _*haarPolynomialValue (matrixPolynomialDerivation (planeGenerator i j) p) U = 0
  rw [haarPolynomialDerivation_zero_at_min p U hmin i j,mul_zero]

end InvariantIsing

end

end OAI

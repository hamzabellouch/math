import OAI.Probability.InvariantIsing.Haar.HaarHeatLinear
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialGamma

namespace OAI

/-! Time differentiation of the squared gradient along the actual polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialHeat_direction_hasDerivAt {N d : ℕ}
    (p : haarPolynomialSpace N d) (A M : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    HasDerivAt (fun s => matrixPolynomialEval M (matrixPolynomialDerivation A
      ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)))
      (matrixPolynomialEval M (matrixPolynomialDerivation A (haarPolynomialLaplacian N
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)))) t :=
  haarPolynomialHeat_linear_hasDerivAt
    ((matrixPolynomialEval M).toLinearMap.comp (matrixPolynomialDerivation A).toLinearMap) p t

lemma haarPolynomialHeat_gamma_hasDerivAt {N d : ℕ}
    (p : haarPolynomialSpace N d) (M : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    HasDerivAt (fun s => matrixPolynomialEval M (haarPolynomialGamma
      ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)
      ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)))
      (2*matrixPolynomialEval M (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        (haarPolynomialLaplacian N
          ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)))) t := by
  have hd (i j : Fin N) := (haarPolynomialHeat_direction_hasDerivAt p (planeGenerator i j) M t).pow 2
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hd i j
  convert hs using 1
  · funext s
    simp only [haarPolynomialGamma,map_sum,map_mul,pow_two]
    rfl
  · simp only [haarPolynomialGamma,map_sum,map_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.cast_ofNat]
    ring

end InvariantIsing

end

end OAI

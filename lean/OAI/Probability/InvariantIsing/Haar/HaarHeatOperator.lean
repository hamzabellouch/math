import OAI.Probability.InvariantIsing.Haar.HaarHeatContinuity
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialGamma

namespace OAI

/-! Joint continuity of differentiated heat polynomials and their squared gradient. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialOperator_eval_coordinates {N d : ℕ}
    (A : Module.End ℝ (MatrixPolynomial N)) (p : haarPolynomialSpace N d)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (A (p : MatrixPolynomial N)) =
      ∑ i, haarPolynomialCoordinates N d p i*
        matrixPolynomialEval M (A (haarPolynomialBasis N d i)) := by
  have hp : p = ∑ i, haarPolynomialCoordinates N d p i •
      (Module.finBasis ℝ (haarPolynomialSpace N d)) i := by
    simpa only [haarPolynomialCoordinates,LinearEquiv.symm_apply_apply] using
      (Module.finBasis ℝ (haarPolynomialSpace N d)).equivFun_symm_apply
        (haarPolynomialCoordinates N d p)
  conv_lhs => rw [hp]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,
    haarPolynomialBasis]

lemma continuous_haarPolynomialHeat_operator_value {N d : ℕ}
    (A : Module.End ℝ (MatrixPolynomial N)) (p : haarPolynomialSpace N d) :
    Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue
      (A ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N)) z.2) := by
  have hc := continuous_haarPolynomialHeat_coordinates p
  have hs : Continuous (fun z : ℝ × SpecialOrthogonal N =>
      ∑ i, haarPolynomialCoordinates N d (haarPolynomialHeat N d z.1 p) i*
        haarPolynomialValue (A (haarPolynomialBasis N d i)) z.2) := by
    apply continuous_finsetSum
    intro i _
    exact (((continuous_apply i).comp hc).comp continuous_fst).mul
      ((continuous_haarPolynomialValue _).comp continuous_snd)
  convert hs using 1
  funext z
  exact haarPolynomialOperator_eval_coordinates _ _ _

lemma continuous_haarPolynomialHeat_gamma {N d : ℕ} (p : haarPolynomialSpace N d) :
    Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue
      (haarPolynomialGamma
        ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N)) z.2) := by
  have hs : Continuous (fun z : ℝ × SpecialOrthogonal N =>
      ∑ i : Fin N, ∑ j : Fin N,
        (haarPolynomialValue (matrixPolynomialDerivation (planeGenerator i j)
          ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N)) z.2)^2) := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (continuous_haarPolynomialHeat_operator_value
      (matrixPolynomialDerivation (planeGenerator i j)).toLinearMap p).pow 2
  convert hs using 1
  funext z
  simp only [haarPolynomialValue,haarPolynomialGamma,map_sum,map_mul,pow_two]

end InvariantIsing

end

end OAI

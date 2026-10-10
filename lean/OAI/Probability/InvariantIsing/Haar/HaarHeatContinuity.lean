import OAI.Probability.InvariantIsing.Haar.HaarPolynomialHeat

namespace OAI

/-! Joint continuity of the finite polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def haarPolynomialBasis (N d : ℕ)
    (i : Fin (Module.finrank ℝ (haarPolynomialSpace N d))) : MatrixPolynomial N :=
  ((Module.finBasis ℝ (haarPolynomialSpace N d)) i : MatrixPolynomial N)

lemma haarPolynomialEval_eq_coordinates {N d : ℕ}
    (p : haarPolynomialSpace N d) (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (p : MatrixPolynomial N) =
      ∑ i, haarPolynomialCoordinates N d p i*
        matrixPolynomialEval M (haarPolynomialBasis N d i) := by
  have hp : p = ∑ i, haarPolynomialCoordinates N d p i •
      (Module.finBasis ℝ (haarPolynomialSpace N d)) i := by
    simpa only [haarPolynomialCoordinates,LinearEquiv.symm_apply_apply] using
      ((Module.finBasis ℝ (haarPolynomialSpace N d)).equivFun_symm_apply
        (haarPolynomialCoordinates N d p))
  conv_lhs => rw [hp]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,
    haarPolynomialBasis]

lemma continuous_haarPolynomialHeat_coordinates {N d : ℕ} (p : haarPolynomialSpace N d) :
    Continuous (fun t : ℝ => haarPolynomialCoordinates N d (haarPolynomialHeat N d t p)) := by
  let L := haarPolynomialCoordinateLaplacian N d
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • L)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exp_smul_const' L t).continuousAt
  have hh := hc.clm_apply (continuous_const (y := haarPolynomialCoordinates N d p))
  simpa only [haarPolynomialCoordinates_heat] using hh

lemma continuous_haarPolynomialHeat_value {N d : ℕ} (p : haarPolynomialSpace N d) :
    Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue
      ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N) z.2) := by
  have hc := continuous_haarPolynomialHeat_coordinates p
  have hs : Continuous (fun z : ℝ × SpecialOrthogonal N =>
      ∑ i, haarPolynomialCoordinates N d (haarPolynomialHeat N d z.1 p) i*
        haarPolynomialValue (haarPolynomialBasis N d i) z.2) := by
    apply continuous_finsetSum
    intro i _
    exact (((continuous_apply i).comp hc).comp continuous_fst).mul
      ((continuous_haarPolynomialValue _).comp continuous_snd)
  convert hs using 1
  funext z
  exact haarPolynomialEval_eq_coordinates _ _

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Haar.HaarPolynomialCurvature

namespace OAI

/-! The curvature estimate survives a symmetric gradient-square correction. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma matrixPolynomial_corrected_hessian_bound {N : ℕ}
    (p : MatrixPolynomial N) (M : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    ((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
      ∑ i, ∑ j, ∑ k, ∑ l,
        (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator k l)
          (matrixPolynomialDerivation (planeGenerator i j) p))-
          c*matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p)*
            matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator k l) p))^2 := by
  let ell := matrixPolynomialDifferential p M
  let H : (Fin N × Fin N) → (Fin N × Fin N) → ℝ := fun a b =>
    matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator b.1 b.2)
      (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))-
      c*ell (planeGenerator a.1 a.2)*ell (planeGenerator b.1 b.2)
  have hd (a b : Fin N × Fin N) : H a b-H b a =
      ell (planeGenerator a.1 a.2*planeGenerator b.1 b.2-
        planeGenerator b.1 b.2*planeGenerator a.1 a.2) := by
    have he := congrArg (matrixPolynomialEval M) (Derivation.congr_fun
      (matrixPolynomialDerivation_commutator
        (planeGenerator b.1 b.2) (planeGenerator a.1 a.2)) p)
    change matrixPolynomialEval M (_-_) = _ at he
    rw [map_sub] at he
    change matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator b.1 b.2)
        (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))-
      matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator a.1 a.2)
        (matrixPolynomialDerivation (planeGenerator b.1 b.2) p)) = _ at he
    dsimp only [H,ell,matrixPolynomialDifferential,LinearMap.coe_mk,AddHom.coe_mk]
    linear_combination he
  have hb := sum_antisymmetric_square_le H
  simp_rw [hd] at hb
  simp only [Fintype.sum_prod_type] at hb
  rw [sum_plane_functional_double_bracket_sq ell] at hb
  have hg : (∑ i : Fin N, ∑ j : Fin N, (ell (planeGenerator i j))^2) =
      matrixPolynomialEval M (haarPolynomialGamma p p) := by
    simp only [haarPolynomialGamma,map_sum,map_mul,pow_two]
    rfl
  rw [hg] at hb
  dsimp only [H,ell,matrixPolynomialDifferential,LinearMap.coe_mk,AddHom.coe_mk] at hb
  linarith

end InvariantIsing

end

end OAI

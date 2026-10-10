import OAI.Combinatorics.Crossing.BivariateCoefficients

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators

abbrev TriangleIndex (s : ℕ) := ↥(twoTriangle s)

def triangleCoordEquiv (s : ℕ) : BiExponent s ≃ TriangleIndex s :=
  Fintype.equivOfCardEq (by simp [BiExponent, TriangleIndex, card_twoTriangle])

def monomialVector (s : ℕ) (node : ℕ → ℝ) (p q : ℕ) : BiExponent s → ℝ :=
  fun ab => node p ^ ab.1.val * node q ^ ab.2.val

def triangleMatrix (s : ℕ) (node : ℕ → ℝ) : Matrix (BiExponent s) (BiExponent s) ℝ :=
  fun ab j => monomialVector s node (triangleCoordEquiv s j).val.1
    (triangleCoordEquiv s j).val.2 ab

theorem triangleMatrix_eval (s : ℕ) (node : ℕ → ℝ) (c : BiExponent s → ℝ)
    (j : BiExponent s) :
    (triangleMatrix s node).transpose.mulVec c j =
      biEval (node (triangleCoordEquiv s j).val.1) (node (triangleCoordEquiv s j).val.2)
        (biOfCoeffs s c) := by
  rw [biEval_biOfCoeffs]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, triangleMatrix,
    monomialVector, Fintype.sum_prod_type]

theorem triangleMatrix_isUnit (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) : IsUnit (triangleMatrix s node) := by
  rw [← Matrix.isUnit_transpose, ← Matrix.mulVec_injective_iff_isUnit]
  intro c d hcd
  apply biOfCoeffs_injective s
  apply twoTriangle_evaluation_injective s node hn (biOfCoeffs s c) (biOfCoeffs s d)
    (biOfCoeffs_bounded s c) (biOfCoeffs_bounded s d)
  intro p q hpq
  let j := (triangleCoordEquiv s).symm ⟨(p,q), hpq⟩
  have hh := congrFun hcd j
  rw [triangleMatrix_eval, triangleMatrix_eval] at hh
  simpa only [j, Equiv.apply_symm_apply] using hh

def twoTriangleBasis (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) :
    Basis (BiExponent s) ℝ (BiExponent s → ℝ) :=
  (Pi.basisFun ℝ (BiExponent s)).map
    (LinearEquiv.ofBijective (triangleMatrix s node).mulVecLin
      ⟨Matrix.mulVec_injective_of_isUnit (triangleMatrix_isUnit s node hn),
        Matrix.mulVec_surjective_iff_isUnit.mpr (triangleMatrix_isUnit s node hn)⟩)

theorem twoTriangleBasis_apply (s : ℕ) (node : ℕ → ℝ)
    (hn : Set.InjOn node (Set.Icc 1 (2*s+1))) (j : BiExponent s) :
    twoTriangleBasis s node hn j =
      monomialVector s node (triangleCoordEquiv s j).val.1 (triangleCoordEquiv s j).val.2 := by
  simp only [twoTriangleBasis, Basis.map_apply, Pi.basisFun_apply]
  change (triangleMatrix s node).mulVec (Pi.single j 1) = _
  funext i
  simp [Matrix.mulVec_single, triangleMatrix]

end Zarankiewicz

end

end OAI

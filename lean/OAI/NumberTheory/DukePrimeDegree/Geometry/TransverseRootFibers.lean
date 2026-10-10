import OAI.NumberTheory.DukePrimeDegree.Geometry.TransverseDiagonalData
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootGlobalCoordinates

namespace OAI

/-! # Transverse coordinates of actual right root displacements

The transverse coordinate is constant on a right upper-unipotent leaf.
A right diagonal displacement translates its logarithmic diagonal exactly.
These identities allow return refinements to use transverse cells only.
-/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem transverse_eq_of_right_upperRoot {n : ℕ}
    (s r : UpperRootTransverse n) (u v : UpperRootTime n)
    (h : positiveRootGeneratedGroup (allPositiveRoots n))
    (he : upperRootParam n (s,u)*h.val=upperRootParam n (r,v)) : s=r := by
  obtain ⟨w,hw⟩ := upperRootWord_surjective n
    ⟨(completeRootChain n).word u*h.val,
      (positiveRootGeneratedGroup _).mul_mem (upperRootWord_mem n u) h.prop⟩
  have he' : upperRootParam n (s,w)=upperRootParam n (r,v) := by
    rw [upperRootParam_eq_mul,hw,←mul_assoc,←upperRootParam_eq_mul]
    exact he
  exact congrArg Prod.fst ((upperRootParam_isOpenEmbedding n).injective he')

theorem transverse_eq_of_right_diagonal_upperRoot {n : ℕ}
    (s r : UpperRootTransverse n) (u v : UpperRootTime n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (t : ℝ)
    (h : positiveRootGeneratedGroup (allPositiveRoots n))
    (he : upperRootParam n (s,u)*(diagonalOneParameter ell hell t*h.val)=
      upperRootParam n (r,v)) :
    r=upperRootTransverseDiagonal ell hell t s := by
  let u' := (completeRootChain n).rootDilation ell (-t) u
  have hp : upperRootParam n (upperRootTransverseDiagonal ell hell t s,u')=
      upperRootParam n (s,u)*diagonalOneParameter ell hell t := by
    rw [upperRootParam_eq_mul,upperRootParam_eq_mul]
    change (s.val*diagonalOneParameter ell hell t)*(completeRootChain n).word u'=_
    dsimp only [u']
    rw [(completeRootChain n).word_rootDilation ell hell (-t),neg_neg,
      diagonalOneParameter_neg]
    group
  apply Eq.symm
  apply transverse_eq_of_right_upperRoot _ _ u' v h
  rw [hp,mul_assoc]
  exact he

theorem transverseLogDiagonal_right_diagonal_upperRoot {n : ℕ}
    (s r : UpperRootTransverse n) (u v : UpperRootTime n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (t : ℝ)
    (h : positiveRootGeneratedGroup (allPositiveRoots n))
    (he : upperRootParam n (s,u)*(diagonalOneParameter ell hell t*h.val)=
      upperRootParam n (r,v)) :
    transverseLogDiagonal r=fun i => transverseLogDiagonal s i+ell i*t := by
  rw [transverse_eq_of_right_diagonal_upperRoot s r u v ell hell t h he]
  exact transverseLogDiagonal_diagonal ell hell t s

end DukePrimeDegree

end

end OAI

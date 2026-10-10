import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.CompletelyPositiveOperations

namespace OAI

section

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace CompletelyPositiveOperations
variable {E D : Type*} [CStarAlgebra E] [CStarAlgebra D]
  [PartialOrder E] [StarOrderedRing E] [PartialOrder D] [StarOrderedRing D]
variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixKraus (p : n) (v : n → E) : CStarMatrix n n ℂ →CP E :=
  comp (corner p) (comp
    (conjugate (CStarMatrix.ofMatrix (fun i j => if j=p then star (v i) else 0)))
    ((CStarMatrix.mapₙₐ (n := n) (StarAlgHom.ofId ℂ E).toNonUnitalStarAlgHom) :
      CStarMatrix n n ℂ →CP CStarMatrix n n E))

lemma matrixKraus_apply (p : n) (v : n → E) (a : CStarMatrix n n ℂ) :
    matrixKraus p v a=∑ i : n, ∑ j : n, (a i j) • (v i*star (v j)) := by
  change ((star (CStarMatrix.ofMatrix (fun i j => if j=p then star (v i) else 0)) *
    (CStarMatrix.mapₙₐ (n := n) (StarAlgHom.ofId ℂ E).toNonUnitalStarAlgHom a)) *
    CStarMatrix.ofMatrix (fun i j => if j=p then star (v i) else 0)) p p=_
  simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply,CStarMatrix.mapₙₐ_apply,
    CStarMatrix.mapₗ_apply,CStarMatrix.map_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change star (if p=p then star (v i) else 0)*algebraMap ℂ E (a i j)*
    (if p=p then star (v j) else 0)=_
  simp only [ite_true,star_star,Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one,
    smul_mul_assoc]

def matrixUnit (i j : n) : CStarMatrix n n ℂ := CStarMatrix.ofMatrix (Matrix.single i j 1)

lemma matrixUnit_mul (i j k : n) : matrixUnit i k*matrixUnit k j=matrixUnit i j := by
  have product_eq : Matrix.single i k (1 : ℂ) * Matrix.single k j 1 =
      Matrix.single i j 1 := by
    simpa only [one_mul] using (Matrix.single_mul_single_same (c := (1 : ℂ)) i k j 1)
  exact congrArg CStarMatrix.ofMatrix product_eq

omit [Fintype n] in
lemma matrixUnit_star (i j : n) : star (matrixUnit i j)=matrixUnit j i := by
  change Matrix.conjTranspose (Matrix.single i j (1 : ℂ)) = Matrix.single j i 1
  simp only [Matrix.conjTranspose_single, star_one]

lemma matrix_decomposition (a : CStarMatrix n n ℂ) :
    a=∑ i : n, ∑ j : n, (a i j) • matrixUnit i j := by
  ext k l
  simp [matrix_sum_apply,matrixUnit,Matrix.single_apply,ite_and]

omit [PartialOrder D] [StarOrderedRing D] in

theorem matrixKraus_lift (q : E →⋆ₐ[ℂ] D) (π : CStarMatrix n n ℂ →⋆ₐ[ℂ] D)
    (p : n) (v : n → E) (hv : ∀ i, q (v i)=π (matrixUnit i p)) :
    ∀ a, q (matrixKraus p v a)=π a := by
  intro a
  rw [matrixKraus_apply]
  simp only [_root_.map_sum,_root_.map_smul,_root_.map_mul,StarHomClass.map_star,hv,
    ←StarHomClass.map_star π,matrixUnit_star,←_root_.map_mul π,matrixUnit_mul]
  conv_rhs => rw [matrix_decomposition a]
  simp only [_root_.map_sum,_root_.map_smul]

end CompletelyPositiveOperations

end
end

end OAI

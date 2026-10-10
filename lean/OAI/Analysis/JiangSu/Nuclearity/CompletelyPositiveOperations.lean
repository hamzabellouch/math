import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights

namespace OAI

section

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace CompletelyPositiveOperations
variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [PartialOrder A] [PartialOrder B] [PartialOrder C]
  [StarOrderedRing A] [StarOrderedRing B] [StarOrderedRing C]

def comp (g : B →CP C) (f : A →CP B) : A →CP C where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_cstarMatrix_nonneg' _ M hM := by
    exact g.map_cstarMatrix_nonneg (M.map f) (f.map_cstarMatrix_nonneg M hM)

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrix_sum_apply {ι m n : Type*} (s : Finset ι) (f : ι → CStarMatrix m n A) (i : m) (j : n) :
    (∑ t ∈ s, f t) i j=∑ t ∈ s, f t i j := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert t s ht ih =>
    rw [Finset.sum_insert ht,Finset.sum_insert ht,CStarMatrix.add_apply,ih]

def conjugate (v : A) : A →CP A where
  toFun x := star v*x*v
  map_add' x y := by noncomm_ring
  map_smul' c x := by simp only [mul_smul_comm,smul_mul_assoc,RingHom.id_apply]
  map_cstarMatrix_nonneg' k M hM := by
    let V : CStarMatrix (Fin k) (Fin k) A := CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => v))
    have he : M.map (fun x => star v*x*v)=star V*M*V := by
      ext i j
      change star v*(M i j)*v=(Matrix.conjTranspose (Matrix.diagonal (fun _ : Fin k => v)) *
        CStarMatrix.ofMatrix.symm M * Matrix.diagonal (fun _ : Fin k => v)) i j
      simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul,Matrix.mul_diagonal,Pi.star_apply,CStarMatrix.ofMatrix_symm_apply]
    change 0≤M.map (fun x => star v*x*v)
    rw [he]
    exact star_left_conjugate_nonneg hM V

def corner {n : Type*} [Fintype n] (p : n) : CStarMatrix n n A →CP A where
  toFun M := M p p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_cstarMatrix_nonneg' k M hM := by
    let : Module ℝ (CStarMatrix (Fin k) (Fin k) (CStarMatrix n n A)) :=
      Module.compHom _ Complex.ofRealHom
    let S := CFC.sqrt M
    have hS : star S*S=M := by rw [(CFC.sqrt_nonneg M).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self M hM]
    let R (l : n) : CStarMatrix (Fin k) (Fin k) A := CStarMatrix.ofMatrix (fun i j => S i j l p)
    have he : M.map (fun x => x p p)=∑ l : n, star (R l)*R l := by
      rw [←hS]
      ext i j
      simp only [CStarMatrix.map_apply,CStarMatrix.mul_apply,CStarMatrix.star_apply,
        matrix_sum_apply,R]
      exact Finset.sum_comm
    change 0≤M.map (fun x => x p p)
    rw [he]
    exact Finset.sum_nonneg (fun l _ => star_mul_self_nonneg (R l))

lemma cp_map_star (f : A →CP B) (x : A) : f (star x)=star (f x) := by
  obtain ⟨y,hy,_,hxy⟩ := CStarAlgebra.exists_sum_four_nonneg x
  rw [hxy]
  simp only [star_sum,star_smul, _root_.map_sum, _root_.map_smul,
    (fun i => (hy i).isSelfAdjoint.star_eq),
    (fun i => (map_nonneg f (hy i)).isSelfAdjoint.star_eq)]

end CompletelyPositiveOperations

end
end

end OAI

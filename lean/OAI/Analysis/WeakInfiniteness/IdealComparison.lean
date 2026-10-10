import Mathlib
import OAI.Analysis.WeakInfiniteness.FiniteComparison

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma elementCuntzSubequiv_of_le_smul {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {c : ℝ} (hc : 0 ≤ c) (hab : a ≤ c • b) : ElementCuntzSubequiv a b :=
  elementCuntzSubequiv_of_hereditary ha hb (mem_hereditary_of_le_smul b a hb ha hc hab)

lemma sum_cuntz_fiberDiagonal {m : ℕ} (x : Fin m → A) :
    CuntzSubequiv (diagonalCopies 1 (∑ i,x i)) (fiberDiagonal x) := by
  let Y : A → CStarMatrix (Fin m) (Fin 1) A := fun e _ _ => e
  have he : ∀ e : A,(Y e).conjTranspose*fiberDiagonal x*Y e=
      diagonalCopies 1 (star e*(∑ i,x i)*e) := by
    intro e
    ext i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j
    change (∑ k : Fin m,(∑ l : Fin m,star e*Matrix.diagonal x l k)*e)=star e*(∑ i,x i)*e
    simp only [Matrix.diagonal_apply]
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [← Finset.sum_mul,← Finset.mul_sum]
  intro ε hε
  obtain ⟨v,hv⟩ := elementCuntzSubequiv_iff.mp
    (cuntzSubequiv_refl (diagonalCopies 1 (∑ i,x i))) ε hε
  refine ⟨Y v,?_⟩
  rw [he]
  have hn := NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A) 1)
    (star v*(∑ i,x i)*v-∑ i,x i)
  rw [map_sub] at hn
  exact hn.trans_lt hv

omit [PartialOrder A] [StarOrderedRing A] in
def oneBlockColumn (e : A) : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1) A := fun _ _ => e

omit [PartialOrder A] [StarOrderedRing A] in
lemma blockSum_one_sandwich (a b e : A) :
    (oneBlockColumn e).conjTranspose * blockSum (diagonalCopies 1 a) (diagonalCopies 1 b) *
      oneBlockColumn e = diagonalCopies 1 (star e*(a+b)*e) := by
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  simp only [CStarMatrix.mul_apply,CStarMatrix.conjTranspose_apply,oneBlockColumn,
    Fintype.sum_sum_type,Fin.sum_univ_one,blockSum,diagonalCopies,
    CStarMatrix.ofMatrix_apply,Equiv.symm_apply_apply,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.diagonal_apply_eq,
    Matrix.zero_apply,mul_zero,zero_add,add_zero]
  noncomm_ring

lemma sum_two_cuntz_block (a b : A) :
    CuntzSubequiv (diagonalCopies 1 (a+b)) (blockSum (diagonalCopies 1 a) (diagonalCopies 1 b)) := by
  intro ε hε
  obtain ⟨v,hv⟩ := elementCuntzSubequiv_iff.mp
    (cuntzSubequiv_refl (diagonalCopies 1 (a+b))) ε hε
  refine ⟨oneBlockColumn v,?_⟩
  rw [blockSum_one_sandwich]
  have hn := NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A) 1)
    (star v*(a+b)*v-(a+b))
  rw [map_sub] at hn
  exact hn.trans_lt hv

lemma star_add_mul_add_le (x y : A) :
    star (x+y)*(x+y) ≤ (2 : ℝ) • (star x*x+star y*y) := by
  have h := star_mul_self_nonneg (x-y)
  have he : (2 : ℝ) • (star x*x+star y*y)-star (x+y)*(x+y)=star (x-y)*(x-y) := by
    simp only [two_smul,star_sub,star_add]
    noncomm_ring
  exact sub_nonneg.mp (he.symm ▸ h)

lemma star_mul_product_cuntz (a z : A) :
    ElementCuntzSubequiv (star (a*z)*(a*z)) (star z*z) := by
  
  apply (element_initial_cuntz_range (a*z)).trans
  have hc := (cuntzSubequiv_refl (diagonalCopies 1 (z*star z))).sandwich_left (diagonalCopies 1 (star a))
  have he : (diagonalCopies 1 (star a)).conjTranspose*diagonalCopies 1 (z*star z)*diagonalCopies 1 (star a)=
      diagonalCopies 1 ((a*z)*star (a*z)) := by
    change star ((diagonalHom 1) (star a))*(diagonalHom 1) (z*star z)*(diagonalHom 1) (star a)=
      (diagonalHom 1) ((a*z)*star (a*z))
    rw [← map_star,← map_mul,← map_mul,star_star]
    apply congrArg (diagonalHom (A := A) 1)
    rw [star_mul]
    noncomm_ring
  rw [he] at hc
  exact hc.trans (element_range_cuntz_initial z)

end

end WeakPureInfiniteness
end

end OAI

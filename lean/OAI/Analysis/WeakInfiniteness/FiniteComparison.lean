import Mathlib
import OAI.Analysis.WeakInfiniteness.LocalConnection
import OAI.Analysis.WeakInfiniteness.LocalFamily
import OAI.Analysis.WeakInfiniteness.RectangularComparison

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

open scoped CStarAlgebra Topology

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
def fiberDiagonal {m : ℕ} (x : Fin m → A) : CStarMatrix (Fin m) (Fin m) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal x)

omit [PartialOrder A] [StarOrderedRing A] in
lemma continuous_fiberDiagonal (m : ℕ) : Continuous (fiberDiagonal (A := A) (m := m)) := by
  change Continuous (fun x : Fin m → A => Matrix.diagonal x)
  fun_prop

lemma copies_cuntz_fiberDiagonal {m : ℕ} {c : A} {x : Fin m → A}
    (hcx : ∀ i,ElementCuntzSubequiv c (x i)) :
    CuntzSubequiv (diagonalCopies m c) (fiberDiagonal x) := by
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp
    ((continuous_fiberDiagonal (A := A) m).continuousAt (x := fun _ => c)) ε hε
  choose v hv using fun i => elementCuntzSubequiv_iff.mp (hcx i) δ hδ
  refine ⟨fiberDiagonal v,?_⟩
  have he : (fiberDiagonal v).conjTranspose*fiberDiagonal x*fiberDiagonal v=
      fiberDiagonal (fun i => star (v i)*x i*v i) := by
    change (Matrix.diagonal v).conjTranspose*Matrix.diagonal x*Matrix.diagonal v=
      Matrix.diagonal (fun i => star (v i)*x i*v i)
    simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Pi.star_apply]
  rw [he]
  have hd : dist (fun i => star (v i)*x i*v i) (fun _ => c) < δ :=
    (dist_pi_lt_iff hδ).mpr (fun i => by simpa only [dist_eq_norm] using hv i)
  have hout := hcont hd
  rw [dist_eq_norm] at hout
  exact hout

lemma orthogonal_fiberDiagonal_cuntz_sum {m : ℕ} (x : Fin m → A) (hx : ∀ i,0 ≤ x i)
    (hxx : ∀ i j,i ≠ j → x i*x j=0) :
    CuntzSubequiv (fiberDiagonal x) (diagonalCopies 1 (∑ i,x i)) := by
  let R : CStarMatrix (Fin 1) (Fin m) A := fun _ j => CFC.sqrt (x j)
  have hRi : R.conjTranspose*R=fiberDiagonal x := by
    ext i j
    change (∑ k : Fin 1,star (CFC.sqrt (x i))*CFC.sqrt (x j))=Matrix.diagonal x i j
    simp only [Fin.sum_univ_one,(CFC.sqrt_nonneg (x i)).star_eq]
    by_cases hij : i=j
    · subst j
      rw [Matrix.diagonal_apply_eq,CFC.sqrt_mul_sqrt_self _ (hx i)]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact mul_zero_of_hereditary (hx i).isSelfAdjoint (hx j).isSelfAdjoint (hxx i j hij)
        (sqrt_mem_hereditary _ _ (hx i).isSelfAdjoint (self_mem_hereditary _ (hx i)) (hx i))
        (sqrt_mem_hereditary _ _ (hx j).isSelfAdjoint (self_mem_hereditary _ (hx j)) (hx j))
  have hRr : R*R.conjTranspose=diagonalCopies 1 (∑ i,x i) := by
    ext i j
    have hi : i=0 := Subsingleton.elim _ _
    have hj : j=0 := Subsingleton.elim _ _
    subst i; subst j
    change (∑ k : Fin m,CFC.sqrt (x k)*star (CFC.sqrt (x k)))=∑ k : Fin m,x k
    apply Finset.sum_congr rfl
    intro k _
    rw [(CFC.sqrt_nonneg _).star_eq,CFC.sqrt_mul_sqrt_self _ (hx k)]
  rw [← hRi,← hRr]
  exact rectangular_initial_cuntz_range R

lemma copies_cuntz_of_common_orthogonal {m : ℕ} {c h : A} (hh : 0 ≤ h)
    (x : Fin m → A) (hx : ∀ i,0 ≤ x i ∧ x i ∈ hereditarySubalgebra h hh.isSelfAdjoint)
    (hxx : ∀ i j,i ≠ j → x i*x j=0) (hcx : ∀ i,ElementCuntzSubequiv c (x i)) :
    CuntzSubequiv (diagonalCopies m c) (diagonalCopies 1 h) := by
  apply (copies_cuntz_fiberDiagonal hcx).trans
  apply (orthogonal_fiberDiagonal_cuntz_sum x (fun i => (hx i).1) hxx).trans
  exact elementCuntzSubequiv_of_hereditary (Finset.sum_nonneg (fun i _ => (hx i).1)) hh
    ((hereditarySubalgebra h hh.isSelfAdjoint).sum_mem (fun i _ => (hx i).2))

end

end WeakPureInfiniteness
end

end OAI

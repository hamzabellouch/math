import Mathlib
import OAI.Analysis.WeakInfiniteness.CuntzCopies
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

open scoped CStarAlgebra Topology

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma square_zero_two_copies {a x : A} (ha : 0 ≤ a)
    (hx : x ∈ hereditarySubalgebra a ha.isSelfAdjoint) (hxx : x*x=0) :
    CuntzSubequiv (diagonalCopies 2 (star x*x)) (diagonalCopies 1 a) := by
  let D := hereditarySubalgebra a ha.isSelfAdjoint
  have hx' : x ∈ D := hx
  have hxs : star x ∈ D := star_mem hx'
  have hz : star x*x ∈ D := D.mul_mem hxs hx'
  have hw : x*star x ∈ D := D.mul_mem hx' hxs
  have hzw : (star x*x)*(x*star x)=0 := by
    calc
      _ = star x*(x*x)*star x := by noncomm_ring
      _ = 0 := by rw [hxx,mul_zero,zero_mul]
  have hwz : (x*star x)*(star x*x)=0 := by
    simpa only [star_mul,star_star,star_zero] using congrArg star hzw
  let y : Fin 2 → A := ![star x*x,x*star x]
  apply copies_cuntz_of_common_orthogonal ha y
  · intro i
    fin_cases i
    · exact ⟨star_mul_self_nonneg x,hz⟩
    · exact ⟨mul_star_self_nonneg x,hw⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hzw
    · exact hwz
    · exact (hij rfl).elim
  · intro i
    fin_cases i
    · exact cuntzSubequiv_refl _
    · exact element_initial_cuntz_range x

lemma CuntzSubequiv.double_copies {r s : ℕ} {a b : A}
    (hab : CuntzSubequiv (diagonalCopies r a) (diagonalCopies s b)) :
    CuntzSubequiv (diagonalCopies (r+r) a) (diagonalCopies (s+s) b) := by
  have h := (hab.blockSum hab).submatrix_left
    (finSumFinEquiv.symm : Fin (r+r) → Fin r ⊕ Fin r)
  rw [diagonalCopies_double] at h
  have h' := h.reindex_right (finSumFinEquiv.symm : Fin (s+s) ≃ Fin s ⊕ Fin s)
  rwa [diagonalCopies_double] at h'

lemma CuntzSubequiv.power_two_copies {a b : A}
    (hab : ElementCuntzSubequiv a b) (j : ℕ) :
    CuntzSubequiv (diagonalCopies (2^j) a) (diagonalCopies (2^j) b) := by
  induction j with
  | zero => exact hab
  | succ j ih =>
    have h := ih.double_copies
    have he : 2^(j+1)=2^j+2^j := by rw [pow_succ,Nat.mul_two]
    rw [he]
    exact h

lemma CuntzSubequiv.power_two_binary {a b : A}
    (hab : CuntzSubequiv (diagonalCopies 2 a) (diagonalCopies 1 b)) (j : ℕ) :
    CuntzSubequiv (diagonalCopies (2^(j+1)) a) (diagonalCopies (2^j) b) := by
  induction j with
  | zero => exact hab
  | succ j ih =>
    have h := ih.double_copies
    have he : 2^(j+1+1)=2^(j+1)+2^(j+1) := by rw [pow_succ,Nat.mul_two]
    have hf : 2^(j+1)=2^j+2^j := by rw [pow_succ,Nat.mul_two]
    rw [he,hf]
    rw [hf] at h
    exact h

end

end WeakPureInfiniteness
end

end OAI

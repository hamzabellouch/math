import Mathlib
import OAI.Analysis.WeakInfiniteness.CuntzCopies
import OAI.Analysis.WeakInfiniteness.IdealComparison
import OAI.Analysis.WeakInfiniteness.IdealSpan

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

open scoped Topology CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma CuntzSubequiv.copies_of_properlyInfinite_right
    {m : Type*} [Fintype m] {a : A} {H : CStarMatrix m m A}
    (haH : CuntzSubequiv (diagonalCopies 1 a) H) (hH : ProperlyInfinite H) (k : ℕ) :
    CuntzSubequiv (diagonalCopies k a) H := by
  have hp : ∀ j : ℕ,CuntzSubequiv (diagonalCopies (2^j) a) H := by
    intro j
    induction j with
    | zero => exact haH
    | succ j ih =>
      have h := ((ih.blockSum ih).trans hH).submatrix_left
        (finSumFinEquiv.symm : Fin (2^j+2^j) → Fin (2^j) ⊕ Fin (2^j))
      rw [diagonalCopies_double] at h
      have he : 2^(j+1)=2^j+2^j := by rw [pow_succ,Nat.mul_two]
      rw [he]
      exact h
  exact (diagonalCopies_cuntzSubequiv a (Nat.lt_two_pow_self (n := k)).le).trans (hp k)

lemma algebraicIdealSpan_square_cuntz {h : A} (hh : 0 ≤ h) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ProperlyInfinite (diagonalCopies n h)) {x : A} (hx : x ∈ algebraicIdealSpan h) :
    CuntzSubequiv (diagonalCopies 1 (star x*x)) (diagonalCopies n h) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨a,b⟩,rfl⟩ := hy
    have hc : ElementCuntzSubequiv (star (a*h*b)*(a*h*b)) (star (h*b)*(h*b)) := by
      simpa only [mul_assoc] using star_mul_product_cuntz a (h*b)
    apply hc.trans ((element_initial_cuntz_range (h*b)).trans _)
    apply (elementCuntzSubequiv_of_hereditary (mul_star_self_nonneg (h*b)) hh ?_).trans
      (diagonalCopies_cuntzSubequiv h hn)
    have he : (h*b)*star (h*b)=h*(b*star b)*h := by rw [star_mul,hh.star_eq]; noncomm_ring
    rw [he]
    exact sandwich_mem h (b*star b) hh.isSelfAdjoint
  | zero =>
    have he : diagonalCopies 1 (star (0 : A)*0)=0 := by ext i j; simp [diagonalCopies]
    rw [he]
    exact zero_cuntzSubequiv _
  | add x y _ _ hx hy =>
    apply (elementCuntzSubequiv_of_le_smul (star_mul_self_nonneg (x+y))
      (add_nonneg (star_mul_self_nonneg x) (star_mul_self_nonneg y)) (by norm_num : (0 : ℝ) ≤ 2)
      (star_add_mul_add_le x y)).trans
    exact (sum_two_cuntz_block (star x*x) (star y*y)).trans ((hx.blockSum hy).trans hpi)
  | smul c x _ hx =>
    apply (elementCuntzSubequiv_of_hereditary (star_mul_self_nonneg (c•x))
      (star_mul_self_nonneg x) ?_).trans hx
    have hm := (hereditarySubalgebra (star x*x) (star_mul_self_nonneg x).isSelfAdjoint).smul_mem
      (c*star c) (self_mem_hereditary (star x*x) (star_mul_self_nonneg x))
    simp only [star_smul,smul_mul_assoc,mul_smul_comm,smul_smul]
    exact hm

theorem generatedClosedIdeal_copies_cuntz {h x : A} (hh : 0 ≤ h) (hx : 0 ≤ x)
    {n : ℕ} (hn : 1 ≤ n) (hpi : ProperlyInfinite (diagonalCopies n h))
    (hm : x ∈ generatedClosedIdeal h hh.isSelfAdjoint) (k : ℕ) :
    CuntzSubequiv (diagonalCopies k x) (diagonalCopies n h) := by
  have hs : CFC.sqrt x ∈ generatedClosedIdeal h hh.isSelfAdjoint := by
    rw [CFC.sqrt_eq_real_sqrt x hx]
    exact cfcₙ_mem Real.sqrt hm
  have hclosed : IsClosed {a : A | CuntzSubequiv
      (diagonalCopies 1 (star a*a)) (diagonalCopies n h)} := by
    simp only [cuntzSubequiv_iff_mem_closure]
    exact isClosed_closure.preimage
      ((map_continuous (diagonalHom (A := A) 1)).comp (continuous_star.mul continuous_id))
  have hc : CuntzSubequiv (diagonalCopies 1 (star (CFC.sqrt x)*CFC.sqrt x))
      (diagonalCopies n h) :=
    closure_minimal (fun a ha => algebraicIdealSpan_square_cuntz hh hn hpi ha) hclosed hs
  rw [(CFC.sqrt_nonneg x).star_eq,CFC.sqrt_mul_sqrt_self x hx] at hc
  exact hc.copies_of_properlyInfinite_right hpi k

end

end WeakPureInfiniteness
end

end OAI

import Mathlib
import OAI.Analysis.WeakInfiniteness.IndividualInfiniteness
import OAI.Analysis.WeakInfiniteness.UniverseSquareZero

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

open scoped CStarAlgebra Topology InnerProductSpace ComplexOrder

universe u

section UniverseOne

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_binary_splitting_over_norm_slice_any
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ∃ z : A,0 ≤ z ∧ CuntzSubequiv (diagonalCopies (2^j) z) (diagonalCopies 1 a) ∧
      ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),r ≤ ‖π a‖ → π z ≠ 0 := by
  induction j with
  | zero =>
    refine ⟨a,ha,cuntzSubequiv_refl _,?_⟩
    intro H π hπ hnz
    rw [hnz,norm_zero] at hπ
    linarith
  | succ j ih =>
    obtain ⟨z,hz,hza,hzn⟩ := ih
    have hlocal : NonzeroOnNormSlice (hereditarySubalgebra z hz.isSelfAdjoint) a r := by
      intro H π _ hπa
      exact ⟨z,self_mem_hereditary z hz,hz,hzn H π hπa⟩
    obtain ⟨x,hx,hxx,hxn⟩ := exists_square_zero_on_norm_slice_any hA hn hpi
      (hereditarySubalgebra z hz.isSelfAdjoint) (hereditarySubalgebra_inner z hz.isSelfAdjoint) ha hr hlocal
    refine ⟨star x*x,star_mul_self_nonneg x,
      ((square_zero_two_copies hz hx hxx).power_two_binary j).trans hza,?_⟩
    intro H π hπa
    rw [map_mul,map_star]
    exact (CStarRing.star_mul_self_eq_zero_iff (π x)).not.mpr (hxn H π hπa)

theorem exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any
    (hA : Exact A) (hW : WeaklyPurelyInfinite A) {a : A} (ha : 0 ≤ a) :
    ProperlyInfinite (diagonalCopies 1 a) := by
  obtain ⟨n,hn,hpi⟩ := hW
  apply properlyInfinite_of_cuts ha
  intro r hr
  obtain ⟨z,hz,hza,hzn⟩ := exists_binary_splitting_over_norm_slice_any hA hn hpi ha hr n
  have hznn : CuntzSubequiv (diagonalCopies n z) (diagonalCopies 1 a) :=
    (diagonalCopies_cuntzSubequiv z (Nat.lt_two_pow_self (n := n)).le).trans hza
  have hcut : positiveCut r a ∈ generatedClosedIdeal z hz.isSelfAdjoint := by
    apply mem_closed_ideal_of_irreducible_test _
      (NonUnitalStarSubalgebra.isClosed_topologicalClosure _)
      (fun x hx d => generatedClosedIdeal_mul_left z d hz.isSelfAdjoint hx)
      (fun x hx d => generatedClosedIdeal_mul_right z d hz.isSelfAdjoint hx)
      (positiveCut_nonneg r a)
    intro H π _ hπI
    have hpiz : π z=0 := hπI z (self_mem_generatedClosedIdeal z hz)
    have hnorm : ‖π a‖ ≤ r := (lt_of_not_ge (fun h => hzn H π h hpiz)).le
    have he := π.map_cfcₙ (fun t : ℝ => max (t-r) 0) a (by fun_prop)
      (by simpa using max_eq_right (neg_nonpos.mpr hr.le)) (by fun_prop)
      ha.isSelfAdjoint (map_nonneg π ha).isSelfAdjoint
    change π (positiveCut r a)=positiveCut r (π a) at he
    rw [he]
    exact positiveCut_eq_zero_of_norm_le _ hr.le hnorm
  exact (generatedClosedIdeal_copies_cuntz hz (positiveCut_nonneg r a) hn
    (weak_amplification_all hpi hz) hcut 2).trans hznn

end UniverseOne

end

end WeakPureInfiniteness
end

end OAI

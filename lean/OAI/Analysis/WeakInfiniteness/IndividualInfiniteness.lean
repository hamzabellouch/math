import Mathlib
import OAI.Analysis.WeakInfiniteness.IdealComparison2
import OAI.Analysis.WeakInfiniteness.PrimitiveIdealTest
import OAI.Analysis.WeakInfiniteness.SquareZero6
import OAI.Analysis.WeakInfiniteness.SquareZeroComparison

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

universe u

section General

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma properlyInfinite_zero (m : Type*) [Fintype m] :
    ProperlyInfinite (0 : CStarMatrix m m A) := by
  intro ε hε
  refine ⟨0,?_⟩
  have hb : blockSum (0 : CStarMatrix m m A) (0 : CStarMatrix m m A)=0 := by ext i j; cases i <;> cases j <;> rfl
  simpa only [CStarMatrix.mul_zero,CStarMatrix.zero_mul,hb,sub_zero,norm_zero] using hε

lemma weak_amplification_all {n : ℕ}
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {a : A} (ha : 0 ≤ a) : ProperlyInfinite (diagonalCopies n a) := by
  by_cases h : a=0
  · subst a
    have he : diagonalCopies n (0 : A)=0 := (diagonalHom n).map_zero
    rw [he]
    exact properlyInfinite_zero _
  · exact hpi a ha h

lemma norm_sub_positiveCut_le {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 ≤ r) :
    ‖a-positiveCut r a‖ ≤ r := by
  have he : a-positiveCut r a=cfcₙ (fun t : ℝ => t-max (t-r) 0) a := by
    rw [cfcₙ_sub (fun t : ℝ => t) (fun t : ℝ => max (t-r) 0) a
      (by fun_prop) rfl (by fun_prop) (by simpa using (max_eq_right (neg_nonpos.mpr hr)))]
    change a-positiveCut r a=cfcₙ (id : ℝ → ℝ) a-positiveCut r a
    rw [cfcₙ_id ℝ a ha.isSelfAdjoint]
  rw [he]
  apply norm_cfcₙ_le
  intro t ht
  have ht0 : 0 ≤ t := NonnegSpectrumClass.nonneg_of_mem_quasispectrum ha ht
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have : max (t-r) 0 ≤ t := max_le (by linarith) ht0
    linarith
  · have := le_max_left (t-r) 0
    linarith

omit [PartialOrder A] [StarOrderedRing A] in
lemma blockSum_diagonalCopies_one (a : A) :
    matrixSubmatrix (finSumFinEquiv : Fin 1 ⊕ Fin 1 → Fin 2) finSumFinEquiv
      (diagonalCopies 2 a)=blockSum (diagonalCopies 1 a) (diagonalCopies 1 a) := by
  have he := congrArg
    (matrixSubmatrix (finSumFinEquiv : Fin 1 ⊕ Fin 1 → Fin 2) finSumFinEquiv)
      (diagonalCopies_double a 1)
  have hleft : matrixSubmatrix finSumFinEquiv finSumFinEquiv
      (matrixSubmatrix finSumFinEquiv.symm finSumFinEquiv.symm
        (blockSum (diagonalCopies 1 a) (diagonalCopies 1 a)))=
        blockSum (diagonalCopies 1 a) (diagonalCopies 1 a) := by
    ext i j
    simp only [matrixSubmatrix,Equiv.symm_apply_apply]
  rw [hleft] at he
  exact he.symm

lemma properlyInfinite_of_cuts {a : A} (ha : 0 ≤ a)
    (hcuts : ∀ r : ℝ,0 < r →
      CuntzSubequiv (diagonalCopies 2 (positiveCut r a)) (diagonalCopies 1 a)) :
    ProperlyInfinite (diagonalCopies 1 a) := by
  have hc : CuntzSubequiv (diagonalCopies 2 a) (diagonalCopies 1 a) := by
    intro ε hε
    obtain ⟨v,hv⟩ := hcuts (ε/3) (by positivity) (ε/3) (by positivity)
    refine ⟨v,?_⟩
    have hn := NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A) 2)
      (a-positiveCut (ε/3) a)
    rw [map_sub] at hn
    have hn' := norm_sub_positiveCut_le ha (by positivity : 0 ≤ ε/3)
    have he : v.conjTranspose*diagonalCopies 1 a*v-diagonalCopies 2 a =
      (v.conjTranspose*diagonalCopies 1 a*v-diagonalCopies 2 (positiveCut (ε/3) a))+
      (diagonalCopies 2 (positiveCut (ε/3) a)-diagonalCopies 2 a) := by abel
    rw [he]
    have ht := norm_add_le
      (v.conjTranspose*diagonalCopies 1 a*v-diagonalCopies 2 (positiveCut (ε/3) a))
      (diagonalCopies 2 (positiveCut (ε/3) a)-diagonalCopies 2 a)
    rw [norm_sub_rev (diagonalCopies 2 (positiveCut (ε/3) a))] at ht
    exact lt_of_le_of_lt ht (by change ‖_-_‖+‖(diagonalHom 2) a-(diagonalHom 2) (positiveCut (ε/3) a)‖<ε; linarith)
  have h := hc.submatrix_left (finSumFinEquiv : Fin 1 ⊕ Fin 1 → Fin 2)
  rw [blockSum_diagonalCopies_one] at h
  exact h

end General

section UniverseOne

variable {A : Type 1} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_binary_splitting_over_norm_slice_one
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A,0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ∃ z : A,0 ≤ z ∧ CuntzSubequiv (diagonalCopies (2^j) z) (diagonalCopies 1 a) ∧
      ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),r ≤ ‖π a‖ → π z ≠ 0 := by
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
    obtain ⟨x,hx,hxx,hxn⟩ := exists_square_zero_on_norm_slice_one hA hn hpi
      (hereditarySubalgebra z hz.isSelfAdjoint) (hereditarySubalgebra_inner z hz.isSelfAdjoint) ha hr hlocal
    refine ⟨star x*x,star_mul_self_nonneg x,
      ((square_zero_two_copies hz hx hxx).power_two_binary j).trans hza,?_⟩
    intro H π hπa
    rw [map_mul,map_star]
    exact (CStarRing.star_mul_self_eq_zero_iff (π x)).not.mpr (hxn H π hπa)

theorem exact_weaklyPurelyInfinite_individuallyProperlyInfinite_one
    (hA : Exact A) (hW : WeaklyPurelyInfinite A) {a : A} (ha : 0 ≤ a) :
    ProperlyInfinite (diagonalCopies 1 a) := by
  obtain ⟨n,hn,hpi⟩ := hW
  apply properlyInfinite_of_cuts ha
  intro r hr
  obtain ⟨z,hz,hza,hzn⟩ := exists_binary_splitting_over_norm_slice_one hA hn hpi ha hr n
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

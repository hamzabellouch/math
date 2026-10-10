import OAI.GroupTheory.PolycyclicRecognition.Algebra.IrreducibleFiniteTrace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Data.Finset.Sym

namespace OAI

/-! # Finite trace sets for matrices with a common finite exponent

Every trace is a sum of a fixed number of roots from one finite set.
Combined with irreducibility and the trace pairing this proves finiteness.
-/

noncomputable section
namespace PolycyclicRecognition

theorem finite_trace_of_charpoly_roots_subset
    {K X I : Type*} [Field K] [IsAlgClosed K] [Fintype I] [DecidableEq I]
    (A : X → Matrix I I K) (s : Finset K)
    (hroots : ∀ x z, z ∈ (A x).charpoly.roots → z ∈ s) :
    (Set.range (fun x => Matrix.trace (A x))).Finite := by
  classical
  let S := (s.sym (Fintype.card I)).image (fun m => m.val.sum)
  apply S.finite_toSet.subset
  rintro _ ⟨x, rfl⟩
  have hc : (A x).charpoly.roots.card = Fintype.card I := by
    rw [← (IsAlgClosed.splits (A x).charpoly).natDegree_eq_card_roots]
    exact Matrix.charpoly_natDegree_eq_dim (A x)
  let m : Sym K (Fintype.card I) := ⟨(A x).charpoly.roots, hc⟩
  have hm : m ∈ s.sym (Fintype.card I) := Finset.mem_sym_iff.mpr (hroots x)
  exact Finset.mem_image.mpr ⟨m, hm, (Matrix.trace_eq_sum_roots_charpoly (A x)).symm⟩

theorem charpoly_root_power_eq_one
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (A : Matrix I I K) (m : ℕ) (hA : A ^ m = 1)
    {z : K} (hz : z ∈ A.charpoly.roots) : z ^ m = 1 := by
  let e := Matrix.toLinAlgEquiv' (R := K) (n := I)
  let T : Module.End K (I → K) := e A
  have hcp : T.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have heig : T.HasEigenvalue z := (Module.End.hasEigenvalue_iff_isRoot_charpoly T z).mpr (by
    rw [hcp]
    exact (Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hz)
  obtain ⟨v, hv, hv0⟩ := heig.exists_hasEigenvector
  have hp : T ^ m = 1 := by
    have hh := congrArg e hA
    simpa only [map_pow, map_one] using hh
  apply smul_left_injective K hv0
  have hh := (show T.HasEigenvector z v from ⟨hv, hv0⟩).pow_apply m
  rw [hp] at hh
  simpa only [Module.End.one_apply, one_smul] using hh.symm

theorem finite_trace_of_common_matrix_exponent
    {K X I : Type*} [Field K] [IsAlgClosed K] [Fintype I] [DecidableEq I]
    (A : X → Matrix I I K) (m : ℕ) (hm : 0 < m) (hA : ∀ x, A x ^ m = 1) :
    (Set.range (fun x => Matrix.trace (A x))).Finite := by
  classical
  apply finite_trace_of_charpoly_roots_subset A (Polynomial.nthRoots m (1 : K)).toFinset
  intro x z hz
  apply Multiset.mem_toFinset.mpr
  exact (Polynomial.mem_nthRoots hm).mpr (charpoly_root_power_eq_one (A x) m (hA x) hz)

namespace PolynomialMatrixGroup

theorem finite_of_irreducible_common_exponent
    {K G : Type*} [Field K] [IsAlgClosed K] [Group G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Function.Injective ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (linearAction.toMonoidHom.comp ι))]
    (m : ℕ) (hm : 0 < m) (hpow : ∀ g : G, g ^ m = 1) : Finite G := by
  apply finite_of_irreducible_finite_trace ι hι
  apply finite_trace_of_common_matrix_exponent (fun g => entries (ι g)) m hm
  intro g
  let E : PolynomialMatrixGroup K n →* Matrix (Fin n) (Fin n) K := {
    toFun := entries
    map_one' := rfl
    map_mul' := entries_mul }
  have hh := congrArg E (congrArg ι (hpow g))
  change E (ι g) ^ m = 1
  simpa only [map_pow, map_one] using hh

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI

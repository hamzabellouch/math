import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteExponentLinearGroups
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionEigenvaluesUnipotentPower
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.FieldTheory.Separable

namespace OAI

/-! # A common exponent from a finite set of torsion eigenvalues

Finite-order matrices have separable minimal polynomials in characteristic
zero. Thus a common period of their eigenvalues is a period of the matrices
themselves, without a bound on the individual orders as an extra hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition
open Polynomial

theorem torsion_matrix_power_eq_one_of_roots
    {K I : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    [Fintype I] [DecidableEq I] (A : Matrix I I K)
    (hA : ∃ r : ℕ, 0 < r ∧ A ^ r = 1) (m : ℕ) (hm : 0 < m)
    (hroots : ∀ z ∈ A.charpoly.roots, z ^ m = 1) : A ^ m = 1 := by
  obtain ⟨r, hr, hAr⟩ := hA
  have hd : minpoly K A ∣ (X ^ r - 1 : K[X]) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, map_one, hAr, sub_self]
  have hs : (minpoly K A).Separable :=
    (X_pow_sub_one_separable_iff.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr))).of_dvd hd
  have hq : (X ^ m - 1 : K[X]) ≠ 0 := by
    exact X_pow_sub_C_ne_zero hm 1
  have hdiv : minpoly K A ∣ (X ^ m - 1 : K[X]) := by
    apply (IsAlgClosed.splits _).dvd_of_roots_le_roots (minpoly.monic A.isIntegral).ne_zero
    apply (Multiset.le_iff_subset (nodup_roots hs)).mpr
    intro z hz
    apply (mem_roots hq).mpr
    have hc : z ∈ A.charpoly.roots :=
      Multiset.subset_of_le
        (roots.le_of_dvd A.charpoly_monic.ne_zero A.minpoly_dvd_charpoly) hz
    simpa only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] using hroots z hc
  have he := (minpoly.dvd_iff (A := K) (x := A)).mp hdiv
  simpa only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] using he

theorem common_exponent_of_torsion_matrix_roots
    {K X I : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    [Fintype I] [DecidableEq I] (A : X → Matrix I I K)
    (hA : ∀ x, ∃ r : ℕ, 0 < r ∧ A x ^ r = 1)
    (s : Finset K) (hs : ∀ z ∈ s, ∃ r : ℕ, 0 < r ∧ z ^ r = 1)
    (hroots : ∀ x z, z ∈ (A x).charpoly.roots → z ∈ s) :
    ∃ m : ℕ, 0 < m ∧ ∀ x, A x ^ m = 1 := by
  obtain ⟨m, hm, hp⟩ := finite_torsion_common_power s hs
  exact ⟨m, hm, fun x => torsion_matrix_power_eq_one_of_roots (A x) (hA x) m hm
    (fun z hz => hp z (hroots x z hz))⟩

end PolycyclicRecognition

end

end OAI

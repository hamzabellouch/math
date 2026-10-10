import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteTypeTorsionEigenvalues
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteCoefficientField

namespace OAI

/-! # Finite traces from torsion spectra

The matrices need not themselves have finite order. Only their eigenvalues
are assumed to be roots of unity. In an irreducible finitely generated
linear group this forces the whole group to be finite.
-/

noncomputable section
namespace PolycyclicRecognition
open Polynomial

theorem finite_trace_of_torsion_spectra
    {K X I : Type} [Field K] [CharZero K] [IsAlgClosed K]
    [Fintype I] [DecidableEq I] (A : X → Matrix I I K)
    (L : IntermediateField ℚ K) [Algebra.EssFiniteType ℚ L]
    (hL : ∀ x i j, A x i j ∈ L)
    (htors : ∀ x z, z ∈ (A x).charpoly.roots → ∃ m : ℕ, 0 < m ∧ z ^ m = 1) :
    (Set.range (fun x => Matrix.trace (A x))).Finite := by
  classical
  obtain ⟨D, hD⟩ := exists_rational_degree_bound_for_roots L
  let S : Set K := {z | (∃ m : ℕ, 0 < m ∧ z ^ m = 1) ∧
    (minpoly ℤ z).natDegree ≤ D * Fintype.card I}
  have hS : S.Finite := finite_rootsOfUnity_of_bounded_degree K (D * Fintype.card I)
  apply finite_trace_of_charpoly_roots_subset A hS.toFinset
  intro x z hz
  apply hS.mem_toFinset.mpr
  change (∃ m : ℕ, 0 < m ∧ z ^ m = 1) ∧
    (minpoly ℤ z).natDegree ≤ D * Fintype.card I
  obtain ⟨m, hm, hp⟩ := htors x z hz
  let B : Matrix I I L := fun i j => ⟨A x i j, hL x i j⟩
  have heB : B.map (algebraMap L K) = A x := rfl
  have hev : aeval z B.charpoly = 0 := by
    have hh := (mem_roots (A x).charpoly_monic.ne_zero).mp hz
    rw [← heB, Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def] at hh
    exact hh
  have hiZ : IsIntegral ℤ z := IsIntegral.of_pow hm (by rw [hp]; exact isIntegral_one)
  have hiQ : IsIntegral ℚ z := IsIntegral.of_pow hm (by rw [hp]; exact isIntegral_one)
  have hd := hD K B.charpoly z B.charpoly_monic.ne_zero hev hiQ
  rw [Matrix.charpoly_natDegree_eq_dim,
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hiZ,
    (minpoly.monic hiZ).natDegree_map] at hd
  exact ⟨⟨m, hm, hp⟩, hd⟩

namespace PolynomialMatrixGroup

theorem finite_of_irreducible_fg_torsion_spectra
    {K G : Type} [Field K] [CharZero K] [IsAlgClosed K]
    [Group G] [Group.FG G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Function.Injective ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (linearAction.toMonoidHom.comp ι))]
    (htors : ∀ g z, z ∈ (entries (ι g)).charpoly.roots →
      ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : Finite G := by
  obtain ⟨L, hL, hentries⟩ := exists_finite_coefficient_field ι
  let : Algebra.EssFiniteType ℚ L := IntermediateField.essFiniteType_iff.mpr hL
  exact finite_of_irreducible_finite_trace ι hι
    (finite_trace_of_torsion_spectra (fun g => entries (ι g)) L hentries htors)

theorem infinite_irreducible_fg_has_nontorsion_eigenvalue
    {K G : Type} [Field K] [CharZero K] [IsAlgClosed K]
    [Group G] [Group.FG G] [Infinite G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Function.Injective ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (linearAction.toMonoidHom.comp ι))] :
    ∃ g : G, ∃ z ∈ (entries (ι g)).charpoly.roots,
      ∀ m : ℕ, 0 < m → z ^ m ≠ 1 := by
  by_contra! h
  have := finite_of_irreducible_fg_torsion_spectra ι hι h
  exact not_finite G

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI

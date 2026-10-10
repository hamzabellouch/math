import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalTorsionEigenvalues
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionMatrixExponent

namespace OAI

/-! # Torsion linear groups over the rationals are finite

Bounded degree gives a single finite set containing every eigenvalue.
Separability converts their common period into an exponent for the group.
The existing finite-exponent theorem does not require irreducibility.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

theorem finite_of_faithful_torsion_finite_eigenvalues
    {K G : Type} [Field K] [CharZero K] [IsAlgClosed K] [Group G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Function.Injective ι)
    (hpow : ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1)
    (s : Finset K) (hs : ∀ z ∈ s, ∃ m : ℕ, 0 < m ∧ z ^ m = 1)
    (hroots : ∀ g z, z ∈ (entries (ι g)).charpoly.roots → z ∈ s) : Finite G := by
  let E : G →* Matrix (Fin n) (Fin n) K := {
    toFun g := entries (ι g)
    map_one' := by rw [map_one]; rfl
    map_mul' g h := by rw [map_mul, entries_mul] }
  have hE (g : G) : ∃ r : ℕ, 0 < r ∧ E g ^ r = 1 := by
    obtain ⟨r, hr, hp⟩ := hpow g
    exact ⟨r, hr, by rw [← map_pow, hp, map_one]⟩
  obtain ⟨m, hm, hp⟩ := common_exponent_of_torsion_matrix_roots E hE s hs hroots
  apply finite_of_faithful_common_exponent n G ι hι m hm
  intro g
  apply hι
  rw [map_pow, map_one]
  apply PolynomialMatrixGroup.ext
  apply Units.ext
  change entries (ι g ^ m) = 1
  have hh : E (g ^ m) = 1 := by rw [map_pow, hp]
  change entries (ι (g ^ m)) = 1 at hh
  rwa [map_pow] at hh

theorem finite_of_faithful_rational_torsion
    {G : Type} [Group G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup ℚ n) (hι : Function.Injective ι)
    (hpow : ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) : Finite G := by
  classical
  let K := AlgebraicClosure ℚ
  let : Algebra ℤ K := Ring.toIntAlgebra K
  let f := algebraMap ℚ K
  let j := (scalarExtension f).comp ι
  let S : Set K := {z | (∃ m : ℕ, 0 < m ∧ z ^ m = 1) ∧
    (minpoly ℤ z).natDegree ≤ n}
  have hS : S.Finite := finite_rootsOfUnity_of_bounded_degree K n
  apply finite_of_faithful_torsion_finite_eigenvalues j
    ((scalarExtension_injective f).comp hι) hpow hS.toFinset
  · intro z hz
    exact ((hS.mem_toFinset).mp hz).1
  · intro g z hz
    apply hS.mem_toFinset.mpr
    have he : entries (j g) = (entries (ι g)).map f := rfl
    rw [he] at hz
    have hA : ∃ m : ℕ, 0 < m ∧ entries (ι g) ^ m = 1 := by
      obtain ⟨m, hm, hp⟩ := hpow g
      let E : G →* Matrix (Fin n) (Fin n) ℚ := {
        toFun g := entries (ι g)
        map_one' := by rw [map_one]; rfl
        map_mul' g h := by rw [map_mul, entries_mul] }
      exact ⟨m, hm, by change E g ^ m = 1; rw [← map_pow, hp, map_one]⟩
    change (∃ m : ℕ, 0 < m ∧ z ^ m = 1) ∧ (minpoly ℤ z).natDegree ≤ n
    simpa only [Fintype.card_fin] using rational_torsion_charpoly_root_integral_degree
      (K := K) (entries (ι g)) hA hz

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI

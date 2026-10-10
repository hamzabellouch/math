import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteTypeTorsionEigenvalues
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalTorsionLinearGroups

namespace OAI

/-! # Torsion linear groups over finitely generated characteristic-zero fields -/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup
open Polynomial

theorem finite_of_faithful_essFiniteType_torsion
    {K G : Type} [Field K] [CharZero K] [Algebra.EssFiniteType ℚ K]
    [Group G] {n : ℕ} (ι : G →* PolynomialMatrixGroup K n)
    (hι : Function.Injective ι)
    (hpow : ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1) : Finite G := by
  classical
  obtain ⟨D, hD⟩ := exists_rational_degree_bound_for_roots K
  let E := AlgebraicClosure K
  let : Algebra ℤ E := Ring.toIntAlgebra E
  let : Algebra ℚ E := DivisionRing.toRatAlgebra
  let f := algebraMap K E
  let j := (scalarExtension f).comp ι
  let S : Set E := {z | (∃ m : ℕ, 0 < m ∧ z ^ m = 1) ∧
    (minpoly ℤ z).natDegree ≤ D * n}
  have hS : S.Finite := finite_rootsOfUnity_of_bounded_degree E (D * n)
  apply finite_of_faithful_torsion_finite_eigenvalues j
    ((scalarExtension_injective f).comp hι) hpow hS.toFinset
  · intro z hz
    exact ((hS.mem_toFinset).mp hz).1
  · intro g z hz
    apply hS.mem_toFinset.mpr
    change (∃ m : ℕ, 0 < m ∧ z ^ m = 1) ∧ (minpoly ℤ z).natDegree ≤ D * n
    let A := entries (ι g)
    have he : entries (j g) = A.map f := rfl
    rw [he] at hz
    obtain ⟨m, hm, hp⟩ := hpow g
    let T : G →* Matrix (Fin n) (Fin n) E := {
      toFun g := entries (j g)
      map_one' := by rw [map_one]; rfl
      map_mul' g h := by rw [map_mul, entries_mul] }
    have hT : (A.map f) ^ m = 1 := by
      change T g ^ m = 1
      rw [← map_pow, hp, map_one]
    have hzpow := charpoly_root_power_eq_one (A.map f) m hT hz
    have hiZ : IsIntegral ℤ z := IsIntegral.of_pow hm (by rw [hzpow]; exact isIntegral_one)
    have hiQ : IsIntegral ℚ z := IsIntegral.of_pow hm (by rw [hzpow]; exact isIntegral_one)
    have hev : aeval z A.charpoly = 0 := by
      have hh := (mem_roots (A.map f).charpoly_monic.ne_zero).mp hz
      rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def] at hh
      exact hh
    have hd := hD E A.charpoly z A.charpoly_monic.ne_zero hev hiQ
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hiZ,
      (minpoly.monic hiZ).natDegree_map] at hd
    exact ⟨⟨m, hm, hzpow⟩, hd⟩

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI

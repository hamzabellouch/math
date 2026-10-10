import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

/-!
# Pivot coordinates over a field

A surjective family of real linear equations has a set of pivot
coordinates of the same cardinality as the equations. Fixing all other
coordinates leaves at most one solution. This uses linear algebra over
the original field, without reducing a determinant modulo a prime.
-/

namespace TwoPointCorrelations

open Finset Submodule

theorem exists_pivot_coordinates {K ι κ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (T : (ι → K) →ₗ[K] (κ → K)) (hT : Function.Surjective T) :
    ∃ S : Finset ι, S.card = Fintype.card κ ∧
      ∀ x y : ι → K, (∀ i ∉ S, x i = y i) → T x = T y → x = y := by
  classical
  let v : ι → κ → K := fun i => T (Pi.basisFun K ι i)
  have hv : span K (Set.range v) = ⊤ := by
    change span K (Set.range (T ∘ Pi.basisFun K ι)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun K ι).span_eq,
      Submodule.map_top, LinearMap.range_eq_top.mpr hT]
  obtain ⟨η, a, ha, hspan, hind⟩ := exists_linearIndependent' K v
  let : Finite η := Finite.of_injective a ha
  let : Fintype η := Fintype.ofFinite η
  let b : Module.Basis η K (κ → K) := Module.Basis.mk hind (by rw [hspan, hv])
  let S : Finset ι := univ.image a
  have hcard : S.card = Fintype.card κ := by
    rw [show S.card = Fintype.card η by simp [S, card_image_of_injective _ ha]]
    exact (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_pi _)
  refine ⟨S, hcard, ?_⟩
  have hreconstruct (z : ι → K) (hz : ∀ i ∉ S, z i = 0) :
      ∑ j, z (a j) • Pi.basisFun K ι (a j) = z := by
    ext i
    by_cases hi : i ∈ S
    · obtain ⟨j, _, rfl⟩ := mem_image.mp hi
      simp [Pi.basisFun_apply, Pi.single_apply, ha.eq_iff]
    · have hne (j : η) : a j ≠ i := by
        intro heq
        exact hi (mem_image.mpr ⟨j, mem_univ _, heq⟩)
      simp [Pi.basisFun_apply, hne, hz i hi]
  intro x y hxy hTx
  let z := x - y
  have hz (i : ι) (hi : i ∉ S) : z i = 0 := sub_eq_zero.mpr (hxy i hi)
  have hTz : T z = 0 := by simp [z, hTx]
  have hsum : ∑ j, z (a j) • (v ∘ a) j = 0 := by
    rw [show (∑ j, z (a j) • (v ∘ a) j) = T (∑ j, z (a j) • Pi.basisFun K ι (a j)) by
      simp only [map_sum, map_smul, Function.comp_apply, v]]
    rw [hreconstruct z hz, hTz]
  have hc := Fintype.linearIndependent_iff.mp hind (fun j => z (a j)) hsum
  have hz0 : z = 0 := by
    rw [← hreconstruct z hz]
    simp [hc]
  exact sub_eq_zero.mp hz0

end TwoPointCorrelations

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FreeAbelianDuality
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace OAI

/-! # Every abelian subgroup has bounded integral rank

An independent finite family defines an embedded integral lattice. The
cohomological-dimension bound on those lattices bounds the full module rank,
without assuming that the abelian subgroup is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {A : Type} [CommGroup A] {n : ℕ}

def independentLatticeHom (b : Fin n → Additive A) : IntegralLatticeGroup n →* A where
  toFun a := Additive.toMul (Fintype.linearCombination ℤ b a.toAdd)
  map_one' := by change Additive.toMul ((Fintype.linearCombination ℤ b) 0) = 1; simp
  map_mul' a c := congrArg Additive.toMul ((Fintype.linearCombination ℤ b).map_add a.toAdd c.toAdd)

theorem independentLatticeHom_injective {b : Fin n → Additive A}
    (hb : LinearIndependent ℤ b) : Function.Injective (independentLatticeHom b) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  apply hb.fintypeLinearCombination_injective
  exact congrArg Additive.ofMul hxy

theorem abelian_subgroup_integral_rank_le {G : Type} [Group G] (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (H : Subgroup G) [IsMulCommutative H] : Module.rank ℤ (Additive H) ≤ d := by
  by_contra hd
  have hlt : (d : Cardinal) < Module.rank ℤ (Additive H) := lt_of_not_ge hd
  have hle : ((d + 1 : ℕ) : Cardinal) ≤ Module.rank ℤ (Additive H) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Cardinal.natCast_add_one_le_iff.mpr hlt
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank hle
  have hbound := lattice_rank_le_cohomologicalDimension d (d + 1)
    (H.subtype.comp (independentLatticeHom b))
    (Subtype.val_injective.comp (independentLatticeHom_injective hb))
  omega

theorem HasFiniteIntegralCohomologicalDimension.bounds_abelian_subgroup_rank
    {G : Type} [Group G] (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∀ (H : Subgroup G) [IsMulCommutative H], Module.rank ℤ (Additive H) ≤ d := by
  obtain ⟨d, hd⟩ := hG
  let := hd
  exact ⟨d, fun H _ => abelian_subgroup_integral_rank_le d H⟩

end PolycyclicRecognition

end

end OAI

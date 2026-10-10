import OAI.GroupTheory.PolycyclicRecognition.Geometry.RationalRootSurjection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPolyZ

namespace OAI

/-! # Abelian subgroups of nilpotent groups with a finite root core

A finitely generated core meets every abelian subgroup in a finitely
generated subgroup with the same rational span. No torsion-free hypothesis
is needed for this rank statement.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_rootCore_abelian_subgroup_finite
    (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g : G, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H)
    (A : Subgroup G) [IsMulCommutative A] :
    Module.Finite ℚ (RationalAbelianSpace A) := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let J := A.comap H.subtype
  let : Group.FG J := CriticalPercolation.nilpotent_subgroup_fg H J
  let f : J →* A := (H.subtype.comp J.subtype).codRestrict A (fun j => j.property)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : A => (x : G)) he
  let : IsMulCommutative J := ⟨⟨fun a b => hf (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  let : Module.Finite ℤ (Additive J) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  apply Module.Finite.of_surjective (f.toAdditive.toIntLinearMap.baseChange ℚ)
  apply rational_map_surjective_of_roots
  intro a
  obtain ⟨n, hn, hna⟩ := hroot (a : G)
  refine ⟨n, hn, ?_⟩
  let b : J := ⟨⟨(a : G) ^ n, hna⟩, A.pow_mem a.property n⟩
  exact ⟨b, Subtype.ext rfl⟩

end PolycyclicRecognition

end

end OAI

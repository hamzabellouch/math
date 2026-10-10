import OAI.GroupTheory.PolycyclicRecognition.Algebra.AutomorphismExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairedExhaustionIndex
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IncreasingUnionDimension

namespace OAI

/-! # Finite-index refinements of an ascending union

A finite-index subgroup of the base has uniformly bounded index at every
inverse-image stage. Its increasing union therefore still has finite index.
Endomorphism invariance of the base subgroup supplies invariance under the
ambient automorphism.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G] (α : MulAut G) (B : Subgroup G)

def automorphismRestriction (hB : B.map α.toMonoidHom ≤ B) : B →* B where
  toFun b := ⟨α b, hB ⟨b, b.property, rfl⟩⟩
  map_one' := Subtype.ext α.map_one
  map_mul' x y := Subtype.ext (α.map_mul x y)

theorem automorphismStage_relIndex (K : Subgroup G) (n : ℕ) :
    (automorphismStage α K n).relIndex (automorphismStage α B n) = K.relIndex B :=
  Subgroup.relIndex_map_map_of_injective K B ((α⁻¹) ^ n).injective

theorem mappedSubgroup_relIndex (D : Subgroup B) :
    (D.map B.subtype).relIndex B = D.index := by
  have h := Subgroup.relIndex_map_map_of_injective D ⊤ B.subtype_injective
  simpa only [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] using h

theorem mappedSubgroup_automorphism_stable (hB : B.map α.toMonoidHom ≤ B)
    (D : Subgroup B) (hD : D.map (automorphismRestriction α B hB) ≤ D) :
    (D.map B.subtype).map α.toMonoidHom ≤ D.map B.subtype := by
  rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
  exact ⟨automorphismRestriction α B hB d, hD ⟨d, hd, rfl⟩, rfl⟩

theorem finiteIndex_automorphism_iSup_refinement
    (hB : B.map α.toMonoidHom ≤ B)
    (hcover : ∀ g, ∃ n, g ∈ automorphismStage α B n)
    (D : Subgroup B) [D.FiniteIndex] :
    (⨆ n, automorphismStage α (D.map B.subtype) n).FiniteIndex := by
  have hi (n : ℕ) :
      ((automorphismStage α (D.map B.subtype) n).subgroupOf
        (automorphismStage α B n)).index = D.index :=
    (automorphismStage_relIndex α B (D.map B.subtype) n).trans
      (mappedSubgroup_relIndex B D)
  apply finiteIndex_iSup_of_paired_exhaustions (automorphismStage α B)
    (automorphismStage α (D.map B.subtype)) (automorphismStage_monotone α B hB)
    hcover D.index
  · intro n
    exact Subgroup.finiteIndex_iff.mpr ((hi n) ▸ Subgroup.FiniteIndex.index_ne_zero)
  · intro n
    exact (hi n).le

theorem dimension_automorphism_iSup_refinement (hB : B.map α.toMonoidHom ≤ B)
    (D : Subgroup B) (hD : D.map (automorphismRestriction α B hB) ≤ D)
    (d : ℕ) [HasProjectiveDimensionLE (trivialIntegral D) d] :
    HasProjectiveDimensionLE
      (trivialIntegral (⨆ n, automorphismStage α (D.map B.subtype) n : Subgroup G))
      (d + 1) := by
  apply cohomologicalDimension_le_iSup_of_monotone _
    (automorphismStage_monotone α _ (mappedSubgroup_automorphism_stable α B hB D hD)) d
  intro n
  exact cohomologicalDimension_le_of_equiv
    ((D.equivMapOfInjective B.subtype B.subtype_injective).trans
      (automorphismStageEquiv α (D.map B.subtype) n)) d

end PolycyclicRecognition

end

end OAI

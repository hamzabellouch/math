import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIndexHomologyDegree
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NaturalOrientationTransport

namespace OAI

/-! # Index coordinates for nested subgroups with a common orientation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem nestedSubgroup_topHomology_degree {H K : Subgroup G} (hHK : H ≤ K)
    [((H.subgroupOf K)).FiniteIndex] (D : Rep ℤ G) (eD : D.V ≃ₗ[ℤ] ℤ) {n : ℕ}
    (hK : IsIntegralPoincareDualityGroup K n)
    (hD : ∀ A : Rep ℤ K,
      Nonempty (groupHomology A n ≃ₗ[ℤ] (Rep.res K.subtype D ⟶ A))) :
    ∃ (u : groupHomology (Rep.res H.subtype D) n ≃ₗ[ℤ] ℤ)
      (v : groupHomology (Rep.res K.subtype D) n ≃ₗ[ℤ] ℤ),
      ∀ x, v (groupHomology.map (Subgroup.inclusion hHK)
        (subgroupRestrictionMap hHK D) n x) = ((H.subgroupOf K).index : ℤ) * u x := by
  obtain ⟨e, he⟩ := topHomology_natural_prescribed hK (Rep.res K.subtype D) eD hD
  obtain ⟨u, v, hd⟩ := finiteIndex_subgroup_topHomology_degree
    (H.subgroupOf K) (Rep.res K.subtype D) eD e he
  let f := (Subgroup.subgroupOfEquivOfLe hHK).symm
  let s := groupHomology.mapIso (A := Rep.res H.subtype D)
    (B := Rep.res (H.subgroupOf K).subtype (Rep.res K.subtype D)) f
    (LinearEquiv.refl ℤ D.V) (by intro g; rfl) n
  have hs : s.hom ≫ subgroupHomologyInclusion (H.subgroupOf K) (Rep.res K.subtype D) n =
      groupHomology.map (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK D) n := by
    change groupHomology.map _ _ n ≫ groupHomology.map _ _ n = groupHomology.map _ _ n
    rw [← groupHomology.map_comp]
    exact groupHomology.map_congr (by ext; rfl) (by apply DFunLike.ext; intro x; rfl) n
  refine ⟨s.toLinearEquiv.trans u, v, ?_⟩
  intro x
  have hx := congrArg (fun f => f x) hs
  change subgroupHomologyInclusion (H.subgroupOf K) (Rep.res K.subtype D) n (s.hom x) =
    groupHomology.map (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK D) n x at hx
  rw [← hx]
  exact hd (s.hom x)

end PolycyclicRecognition

end

end OAI

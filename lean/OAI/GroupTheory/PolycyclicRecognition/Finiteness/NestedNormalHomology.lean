import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyQuotient

namespace OAI

/-! # Conjugation on homology under nested normal subgroups -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N K : Subgroup G) [N.Normal]
  (hNK : N ≤ K) (A : Rep ℤ G)

def nestedSubgroupHomologyIso (d : ℕ) :
    groupHomology (Rep.res (N.subgroupOf K).subtype (Rep.res K.subtype A)) d ≅
      groupHomology (Rep.res N.subtype A) d :=
  groupHomology.mapIso (A := Rep.res (N.subgroupOf K).subtype (Rep.res K.subtype A))
    (B := Rep.res N.subtype A) (Subgroup.subgroupOfEquivOfLe hNK)
    (LinearEquiv.refl ℤ A.V) (by intro a; rfl) d

theorem nestedSubgroupHomologyIso_conjugation (d : ℕ) (g : K) :
    normalHomologyMap ℤ (N.subgroupOf K) (Rep.res K.subtype A) d g ≫
        (nestedSubgroupHomologyIso N K hNK A d).hom =
      (nestedSubgroupHomologyIso N K hNK A d).hom ≫
        normalHomologyMap ℤ N A d (g : G) := by
  change groupHomology.map _ _ d ≫ groupHomology.map _ _ d =
    groupHomology.map _ _ d ≫ groupHomology.map _ _ d
  rw [← groupHomology.map_comp, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · ext a
    rfl
  · rfl

variable (M : Subgroup K) [M.Normal] (e : M ≃* N)
  (he : ∀ a : M, ((e a : N) : G) = ((a : K) : G))

def embeddedSubgroupHomologyIso (d : ℕ) :
    groupHomology (Rep.res M.subtype (Rep.res K.subtype A)) d ≅
      groupHomology (Rep.res N.subtype A) d :=
  groupHomology.mapIso (A := Rep.res M.subtype (Rep.res K.subtype A))
    (B := Rep.res N.subtype A) e (LinearEquiv.refl ℤ A.V)
    (by intro a; change A.ρ (a : G) = A.ρ (e a : G); rw [he]) d

theorem embeddedSubgroupHomologyIso_conjugation (d : ℕ) (g : K) :
    normalHomologyMap ℤ M (Rep.res K.subtype A) d g ≫
        (embeddedSubgroupHomologyIso N K A M e he d).hom =
      (embeddedSubgroupHomologyIso N K A M e he d).hom ≫
        normalHomologyMap ℤ N A d (g : G) := by
  change groupHomology.map _ _ d ≫ groupHomology.map _ _ d =
    groupHomology.map _ _ d ≫ groupHomology.map _ _ d
  rw [← groupHomology.map_comp, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · ext a
    change ((e (MulAut.conjNormal (H := M) g a) : N) : G) =
      (g : G) * ((e a : N) : G) * (g : G)⁻¹
    rw [he, he]
    rfl
  · rfl

end PolycyclicRecognition

end

end OAI

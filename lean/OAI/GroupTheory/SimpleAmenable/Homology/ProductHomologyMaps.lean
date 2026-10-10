import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.CanonicalProduct

namespace OAI

section

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace ConnectedProduct
open FreeChains AugmentedSplit

variable (X Y : SSet) (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) (n : ℕ)
lemma projection_inclusion (hn : n≠0) [IsIso (projection X Y n)] :
    projection X Y n ≫ inclusion X Y x y n=𝟙 _ := by
  apply (cancel_mono (projection X Y n)).mp
  simp only [Category.assoc,inclusion_projection X Y x y n hn,Category.comp_id,Category.id_comp]
noncomputable def canonicalIso [IsIso (projection X Y n)] :
    (X⊗Y).homology Z n ≅ X.homology Z n ⊞ Y.homology Z n := asIso (projection X Y n)
lemma homologyMap_eq (T : SSet) (f : X⊗Y ⟶ T) (hn : n≠0)
    [IsIso (projection X Y n)] :
    SSet.homologyMap f Z n = projection X Y n ≫
      biprod.desc (SSet.homologyMap (pairLeft X Y y ≫ f) Z n)
        (SSet.homologyMap (pairRight X Y x ≫ f) Z n) := by
  rw [SSet.homologyMap_comp,SSet.homologyMap_comp]
  have hd : biprod.desc (SSet.homologyMap (pairLeft X Y y) Z n ≫ SSet.homologyMap f Z n)
      (SSet.homologyMap (pairRight X Y x) Z n ≫ SSet.homologyMap f Z n) =
      inclusion X Y x y n ≫ SSet.homologyMap f Z n := by
    apply biprod.hom_ext' <;> simp [inclusion]
  rw [hd]
  rw [←Category.assoc,projection_inclusion X Y x y n hn,Category.id_comp]
lemma diagonal_homology_projection (f : X ⟶ X⊗X)
    (h₁ : f ≫ CartesianMonoidalCategory.fst X X=𝟙 X)
    (h₂ : f ≫ CartesianMonoidalCategory.snd X X=𝟙 X) :
    SSet.homologyMap f Z n ≫ projection X X n=biprod.lift (𝟙 _) (𝟙 _) := by
  apply biprod.hom_ext
  · simp only [projection,Category.assoc,biprod.lift_fst,←SSet.homologyMap_comp,h₁,SSet.homologyMap_id]
  · simp only [projection,Category.assoc,biprod.lift_snd,←SSet.homologyMap_comp,h₂,SSet.homologyMap_id]
lemma unit_product_homology (μ : X⊗X ⟶ X)
    (hl : pairLeft X X x ≫ μ=𝟙 X) (hr : pairRight X X x ≫ μ=𝟙 X)
    (hn : n≠0) [IsIso (projection X X n)] :
    SSet.homologyMap μ Z n=projection X X n ≫ biprod.desc (𝟙 _) (𝟙 _) := by
  rw [homologyMap_eq X X x x n X μ hn,hl,hr,SSet.homologyMap_id]
lemma product_naturality {X' Y' : SSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    SSet.homologyMap (f⊗ₘg) Z n ≫ projection X' Y' n=
      projection X Y n ≫ biprod.map (SSet.homologyMap f Z n) (SSet.homologyMap g Z n) := by
  apply biprod.hom_ext
  · simp [projection,Category.assoc,← SSet.homologyMap_comp,
      CartesianMonoidalCategory.tensorHom_fst]
  · simp [projection,Category.assoc,← SSet.homologyMap_comp,
      CartesianMonoidalCategory.tensorHom_snd]
end ConnectedProduct

end

end

end OAI

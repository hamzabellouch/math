import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.DerivedSupport
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasColimitsOfShape (Discrete ℕ) C]
variable {X Y : C} (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X)

private def swindleA : (∐ fun _ : ℕ => Y) ⟶ (∐ fun _ : ℕ => Y) :=
  Sigma.desc fun n => (𝟙 Y - p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) n +
    (p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) (n+1)
private def swindleC : (∐ fun _ : ℕ => Y) ⟶ (∐ fun _ : ℕ => Y) :=
  Sigma.desc fun n => match n with
    | 0 => (𝟙 Y - p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) 0
    | n+1 => (p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) n +
        (𝟙 Y - p ≫ i) ≫ Sigma.ι (fun _ : ℕ => Y) (n+1)
private def swindleB : (∐ fun _ : ℕ => Y) ⟶ X :=
  Sigma.desc fun n => match n with
    | 0 => p
    | _+1 => 0
private def swindleI : X ⟶ (∐ fun _ : ℕ => Y) := i ≫ Sigma.ι (fun _ : ℕ => Y) 0

include hip

private lemma swindleAC : swindleA i p ≫ swindleC i p = 𝟙 _ := by
  apply Sigma.hom_ext
  intro n
  cases n <;>
    simp only [swindleA, swindleC, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc,
      Preadditive.add_comp, Preadditive.comp_add, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.assoc, reassoc_of% hip,
      Category.id_comp, Category.comp_id] <;> abel

private lemma swindleAB : swindleA i p ≫ swindleB p = 0 := by
  apply Sigma.hom_ext
  intro n
  cases n <;> simp [swindleA, swindleB, Preadditive.add_comp, Preadditive.sub_comp,
    Category.assoc, hip]

private lemma swindleIB : swindleI i ≫ swindleB p = 𝟙 _ := by
  simp [swindleI, swindleB, Category.assoc, hip]

private lemma swindleIC : swindleI i ≫ swindleC i p = 0 := by
  simp [swindleI, swindleC, Category.assoc, Preadditive.comp_sub, reassoc_of% hip]

private lemma swindleTotal : swindleC i p ≫ swindleA i p + swindleB p ≫ swindleI i = 𝟙 _ := by
  apply Sigma.hom_ext
  intro n
  cases n <;>
    simp only [swindleA, swindleC, swindleB, swindleI, Sigma.ι_comp_desc_assoc,
      Sigma.ι_comp_desc, Preadditive.add_comp, Preadditive.comp_add,
      Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
      reassoc_of% hip, Category.id_comp, Category.comp_id, zero_comp] <;> abel

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ degree : ℤ, (shiftFunctor C degree).Additive] [Pretriangulated C]

def swindleIso : (∐ fun _ : ℕ => Y) ≅ (∐ fun _ : ℕ => Y) ⊞ X where
  hom := biprod.lift (swindleC i p) (swindleB p)
  inv := biprod.desc (swindleA i p) (swindleI i)
  hom_inv_id := by simpa using swindleTotal i p hip
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp [swindleAC i p hip, swindleAB i p hip,
      swindleIB i p hip, swindleIC i p hip]

lemma swindle_distinguished : Triangle.mk (swindleA i p) (swindleB p) 0 ∈ distTriang C := by
  apply isomorphic_distinguished _ (binaryBiproductTriangle_distinguished (∐ fun _ : ℕ => Y) X)
  refine Triangle.isoMk _ _ (Iso.refl _) (swindleIso i p hip) (Iso.refl _) ?_ ?_ ?_
  · simp only [Triangle.mk, Iso.refl_hom, binaryBiproductTriangle, Category.id_comp]
    change swindleA i p ≫ (swindleIso i p hip).hom = biprod.inl
    apply biprod.hom_ext <;> simp [swindleIso, swindleAC i p hip, swindleAB i p hip]
  · simp only [Triangle.mk, Iso.refl_hom, binaryBiproductTriangle, Category.comp_id]
    change swindleB p = (swindleIso i p hip).hom ≫ biprod.snd
    exact (biprod.lift_snd _ _).symm
  · simp
    exact (Category.id_comp _).symm

lemma localizing_of_retract (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulated] [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] (hY : P Y) : P X := by
  have h : P (∐ fun _ : ℕ => Y) := P.prop_colimit (Discrete.functor (fun _ : ℕ => Y)) (fun _ => hY)
  exact P.ext_of_isTriangulatedClosed₃ _ (swindle_distinguished i p hip) h h

end LittleFinitistic.DerivedSupport

end

end OAI

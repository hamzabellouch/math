import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.FiniteTower
section TowerConstruction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u v
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

abbrev FreeLayer (T : C) : ObjectProperty C :=
  ((ObjectProperty.singleton T).shiftClosure ℤ).binaryProductsClosure

abbrev Thick (T : C) : ObjectProperty C :=
  (ObjectProperty.singleton T).triangEnvelope

inductive Tower (T : C) : C → Prop
  | zero {P : C} (hP : IsZero P) : Tower T P
  | step (tr : Triangle C) (htr : tr ∈ distTriang C)
      (hF : FreeLayer C T tr.obj₁) (tail : Tower T tr.obj₃) : Tower T tr.obj₂

end TowerConstruction
section PretriangulatedClosure
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u v
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]

lemma tower_of_layer (T P : C) (hP : FreeLayer C T P) : Tower C T P := by
  exact Tower.step (contractibleTriangle P) (contractible_distinguished P) hP
    (Tower.zero (isZero_zero C))

lemma tower_of_extension (T : C) (n : ℕ) (P : C)
    (hP : (FreeLayer C T).extensionProductIter n P) : Tower C T P := by
  induction n generalizing P with
  | zero => exact tower_of_layer C T P hP
  | succ n ih =>
      rw [ObjectProperty.extensionProductIter_succ] at hP
      obtain ⟨F, B, f, g, h, ht, hF, hB⟩ := hP
      exact Tower.step (Triangle.mk f g h) ht hF (ih B hB)

theorem tower_normal_form [IsIdempotentComplete C] (T P : C) (hP : Thick C T P) :
    ∃ P₀ : C, Tower C T P₀ ∧ Nonempty (Retract P P₀) := by
  obtain ⟨n, hn⟩ := (ObjectProperty.prop_triangEnvelope_iff _ _).mp hP
  change ((FreeLayer C T).retractClosure.extensionProductIter n).retractClosure P at hn
  rw [ObjectProperty.retractClosure_extensionProductIter_retractClosure] at hn
  obtain ⟨P₀, h₀, hret⟩ := hn
  exact ⟨P₀, tower_of_extension C T n P₀ h₀, hret⟩

end PretriangulatedClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe u v
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

lemma layer_thick (T P : C) (hP : FreeLayer C T P) : Thick C T P := by
  have h : FreeLayer C T ≤ Thick C T := by
    apply (ObjectProperty.binaryProductsClosure_le_iff
      (P := (ObjectProperty.singleton T).shiftClosure ℤ) (Q := Thick C T)).mpr
    apply (ObjectProperty.shiftClosure_le_iff (ObjectProperty.singleton T) (Thick C T) (A := ℤ)).mpr
    exact (ObjectProperty.singleton T).le_triangEnvelope
  exact h P hP

lemma tower_thick (T P : C) (hP : Tower C T P) : Thick C T P := by
  induction hP with
  | zero h => exact (Thick C T).prop_of_isZero h
  | step tr htr hf _ ih =>
      exact (Thick C T).ext_of_isTriangulatedClosed₂ tr htr (layer_thick C T _ hf) ih

end HahnWilson.FiniteTower

end

end OAI

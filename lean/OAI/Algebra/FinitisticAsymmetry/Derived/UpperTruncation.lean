import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Derived.BoundedGeneration

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe u
variable {R : Type u} [Ring R]

def upperSub (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) : Submodule R (K.X j) :=
  if j < a then ⊤ else if j = a then LinearMap.ker (K.d j (j+1)).hom else ⊥

lemma mem_upperSub {K : CochainComplex (ModuleCat.{u} R) ℤ} {a j : ℤ} {x : K.X j} :
    x ∈ upperSub K a j ↔ j < a ∨ (j = a ∧ K.d j (j+1) x = 0) ∨ x = 0 := by
  by_cases h : j < a
  · simp [upperSub, h]
  · by_cases he : j = a
    · simp [upperSub, he, LinearMap.mem_ker]
      intro hx; subst x; exact map_zero _
    · simp [upperSub, h, he]

lemma upperSub_d {K : CochainComplex (ModuleCat.{u} R) ℤ} {a j k : ℤ}
    {x : K.X j} (hx : x ∈ upperSub K a j) : K.d j k x ∈ upperSub K a k := by
  rw [mem_upperSub] at hx ⊢
  by_cases h : (ComplexShape.up ℤ).Rel j k
  · change j + 1 = k at h
    rcases hx with hx | ⟨rfl, hx⟩ | rfl
    · by_cases hk : k < a
      · exact Or.inl hk
      · exact Or.inr (Or.inl ⟨by omega,
          ConcreteCategory.congr_hom (K.d_comp_d j k (k+1)) x⟩)
    · exact Or.inr (Or.inr (by rw [← h]; exact hx))
    · exact Or.inr (Or.inr (map_zero _))
  · rw [K.shape j k h]
    exact Or.inr (Or.inr rfl)

def upper (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    CochainComplex (ModuleCat R) ℤ where
  X j := ModuleCat.of R (upperSub K a j)
  d j k := ModuleCat.ofHom
    { toFun := fun x => ⟨K.d j k x, upperSub_d x.property⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => Subtype.ext (map_smul _ _ _) }
  shape j k hjk := by
    ext x
    change K.d j k x = 0
    rw [K.shape j k hjk]
    rfl
  d_comp_d' j k l hjk hkl := by
    ext x
    exact ConcreteCategory.congr_hom (K.d_comp_d j k l) x

def upperι (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) : upper K a ⟶ K where
  f j := ModuleCat.ofHom (upperSub K a j).subtype
  comm' _ _ _ := rfl

lemma upper_le (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : a ≤ b) (j : ℤ) :
    upperSub K a j ≤ upperSub K b j := by
  intro x hx
  rw [mem_upperSub] at hx ⊢
  rcases hx with hx | ⟨rfl, hx⟩ | rfl
  · exact Or.inl (lt_of_lt_of_le hx h)
  · rcases lt_or_eq_of_le h with hh | rfl
    · exact Or.inl hh
    · exact Or.inr (Or.inl ⟨rfl, hx⟩)
  · exact Or.inr (Or.inr rfl)

def upperMap (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : a ≤ b) :
    upper K a ⟶ upper K b where
  f j := ModuleCat.ofHom (Submodule.inclusion (upper_le K h j))
  comm' _ _ _ := by ext; rfl

@[reassoc (attr := simp)]
lemma upperMap_ι (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ} (h : a ≤ b) :
    upperMap K h ≫ upperι K b = upperι K a := by ext; rfl

lemma upperι_f_isIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) (hj : j < a) :
    IsIso ((upperι K a).f j) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨Subtype.val_injective, fun x => ⟨⟨x, by simp [upperSub, hj]⟩, rfl⟩⟩

lemma upper_isZero_X (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) (hj : a < j) :
    IsZero ((upper K a).X j) := by
  apply ModuleCat.isZero_iff_subsingleton.2
  change Subsingleton (upperSub K a j)
  simp only [upperSub, show ¬ j < a by omega, ↓reduceIte, show ¬ j = a by omega]
  infer_instance

end

universe u w
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

def upperSequenceMap (n : ℕ) : upper K (n : ℤ) ⟶ upper K ((n+1 : ℕ) : ℤ) :=
  upperMap K (by omega)

def upperSequenceCocone : Cocone (Functor.ofSequence (upperSequenceMap K)) where
  pt := K
  ι := NatTrans.ofSequence (fun n => upperι K (n : ℤ)) (fun n => by
    simp [upperSequenceMap]
    exact (upperMap_ι K _).trans (Category.comp_id _).symm)

def upperSequenceIsColimit : IsColimit (upperSequenceCocone K) := by
  apply HomologicalComplex.isColimitOfEval
  intro j
  apply eventuallyIsoCoconeIsColimit _ (j.toNat + 1)
  intro n hn
  change IsIso ((upperι K (n : ℤ)).f j)
  exact upperι_f_isIso K _ _ (by omega)

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]

lemma prop_of_all_modules
    (hM : ∀ (M : ModuleCat R), P ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)) :
    P (DerivedCategory.Q.obj K) := by
  exact localizing_sequence_colimit (fun n => upper K (n : ℤ)) (upperSequenceMap K)
    (upperSequenceCocone K) (upperSequenceIsColimit K) P (fun n =>
      prop_of_boundedAbove_terms P (upper K _) n (upper_isZero_X K _) (fun j => hM _))

lemma localizing_eq_top_of_all_modules
    (hM : ∀ (M : ModuleCat R), P ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M))
    (X : DerivedCategory (ModuleCat R)) : P X := by
  exact P.prop_of_iso (DerivedCategory.Q.objObjPreimageIso X)
    (prop_of_all_modules (DerivedCategory.Q.objPreimage X) P hM)

end LittleFinitistic.DerivedSupport

end

end OAI

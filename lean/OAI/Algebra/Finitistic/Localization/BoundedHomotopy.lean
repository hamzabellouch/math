import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

namespace OAI
noncomputable section
open CategoryTheory Limits ZeroObject Pretriangulated
namespace LittleFinitistic.BoundedHomotopy

variable (C : Type*) [Category* C] [Preadditive C]

/-- Strict boundedness of the underlying complex, at both ends. -/
def boundedComplex : ObjectProperty (CochainComplex C ℤ) :=
  fun X => ∃ a b : ℤ, X.IsStrictlyGE a ∧ X.IsStrictlyLE b

/-- The actual category of bounded cochain complexes, with chain maps. -/
abbrev Complex := (boundedComplex C).FullSubcategory

/-- Bounded representatives, with homotopy classes of chain maps. -/
def bounded : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (boundedComplex C).strictMap (HomotopyCategory.quotient _ _)

@[simp] theorem bounded_quotient_obj_iff (X : CochainComplex C ℤ) :
    bounded C ((HomotopyCategory.quotient _ _).obj X) ↔ boundedComplex C X := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  simp only [bounded, ObjectProperty.strictMap_iff]
  rintro ⟨Y, h, he⟩
  obtain rfl : Y = X := congr_arg CategoryTheory.Quotient.as he
  exact h

instance [HasZeroObject C] : (bounded C).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient _ _).obj 0,
    Functor.map_isZero _ (isZero_zero _), by
      rw [bounded_quotient_obj_iff]
      exact ⟨0, 0, inferInstance, inferInstance⟩⟩

instance : (bounded C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift := by
        intro X hX
        obtain ⟨X : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
        rw [bounded_quotient_obj_iff] at hX
        obtain ⟨a, b, ha, hb⟩ := hX
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
          bounded_quotient_obj_iff]
        exact ⟨a-n, b-n, X.isStrictlyGE_shift a n (a-n) (by omega),
          X.isStrictlyLE_shift b n (b-n) (by omega)⟩ }

variable {C}
theorem bounded_mappingCone [HasBinaryBiproducts C]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (hX : boundedComplex C X) (hY : boundedComplex C Y) :
    boundedComplex C (CochainComplex.mappingCone f) := by
  obtain ⟨a,b,ha,hb⟩ := hX
  obtain ⟨c,d,hc,hd⟩ := hY
  refine ⟨min (a-1) c, max b d, CochainComplex.isStrictlyGE_mappingCone f a c _
    (by omega) (by omega), ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨X.isZero_of_isStrictlyLE b _ (by omega),
    Y.isZero_of_isStrictlyLE d _ (by omega)⟩

variable (C)
instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (bounded C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    have h₁' : boundedComplex C T.obj₁.as := (bounded_quotient_obj_iff _ _).mp h₁
    have h₂' : boundedComplex C T.obj₂.as := (bounded_quotient_obj_iff _ _).mp h₂
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ :=
      (HomotopyCategory.quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_, ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · exact (bounded_quotient_obj_iff _ _).mpr (bounded_mappingCone f h₁' h₂')
    · exact (Category.comp_id _).trans (hf.symm.trans (Category.id_comp _).symm)

instance [HasZeroObject C] [HasBinaryBiproducts C] : (bounded C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The homotopy category Kᵇ(C); boundedness is part of each object. -/
abbrev K := (bounded C).FullSubcategory

/-- Pass from bounded chain maps to their homotopy classes. -/
def quotient : Complex C ⥤ K C :=
  ObjectProperty.lift _ ((boundedComplex C).ι ⋙ HomotopyCategory.quotient _ _)
    (fun X => (bounded_quotient_obj_iff _ _).mpr X.property)

instance [HasZeroObject C] [HasBinaryBiproducts C] : IsTriangulated (K C) := inferInstance

end LittleFinitistic.BoundedHomotopy

end

end OAI

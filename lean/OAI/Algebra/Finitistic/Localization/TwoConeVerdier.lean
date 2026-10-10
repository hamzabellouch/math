import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Localization.Linear

namespace OAI
noncomputable section
open CategoryTheory Limits Pretriangulated Category
namespace LittleFinitistic.TwoConeVerdier

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- Two specified cone triangles, with the first maps the denominators to invert. -/
structure ConePair (C : Type*) [Category* C] [HasShift C ℤ] [Preadditive C]
    [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  first : Triangle C
  second : Triangle C
  first_distinguished : first ∈ distTriang C
  second_distinguished : second ∈ distTriang C

namespace ConePair
variable (T : ConePair C)

/-- Only the two cone objects are generators. -/
def generators : ObjectProperty C := fun X => X = T.first.obj₃ ∨ X = T.second.obj₃
instance : T.generators.Nonempty := ⟨T.first.obj₃, Or.inl rfl⟩

/-- The least thick subcategory containing these two cones. -/
abbrev S : ObjectProperty C := T.generators.triangEnvelope

/-- Exactly the maps whose cone lies in S. -/
abbrev Sigma : MorphismProperty C := T.S.trW

/-- The Verdier localization at the cone class. -/
abbrev Q := T.Sigma.Localization
abbrev q : C ⥤ T.Q := T.Sigma.Q

/-- This is a proved fraction calculus, inherited from the triangle axioms. -/
theorem rightFractions [IsTriangulated C] : T.Sigma.HasRightCalculusOfFractions := inferInstance

theorem quotient_triangulated [IsTriangulated C] : IsTriangulated T.Q := inferInstance

theorem source_localization : T.q.IsLocalization T.Sigma := inferInstance

theorem first_cone_mem : T.S T.first.obj₃ := T.generators.le_triangEnvelope _ (Or.inl rfl)
theorem second_cone_mem : T.S T.second.obj₃ := T.generators.le_triangEnvelope _ (Or.inr rfl)

theorem first_mem : T.Sigma T.first.mor₁ :=
  ObjectProperty.trW.mk _ T.first_distinguished T.first_cone_mem

theorem second_mem : T.Sigma T.second.mor₁ :=
  ObjectProperty.trW.mk _ T.second_distinguished T.second_cone_mem

instance : IsIso (T.q.map T.first.mor₁) := Localization.inverts _ _ _ T.first_mem
instance : IsIso (T.q.map T.second.mor₁) := Localization.inverts _ _ _ T.second_mem

/-- The cone criterion agrees with any distinguished cone triangle. -/
theorem sigma_iff (U : Triangle C) (hU : U ∈ distTriang C) :
    T.Sigma U.mor₁ ↔ T.S U.obj₃ := T.S.trW_iff_of_distinguished U hU

/-- Exact minimality, including closure under retracts. -/
theorem thick_minimal (P : ObjectProperty C) [P.IsTriangulated] [P.IsStableUnderRetracts]
    (h₁ : P T.first.obj₃) (h₂ : P T.second.obj₃) : T.S ≤ P := by
  change T.generators.triangEnvelope ≤ P
  apply (ObjectProperty.triangEnvelope_le_iff T.generators (Q := P)).mpr
  intro X hX
  rcases hX with rfl | rfl <;> assumption

/-- Every morphism is a roof with a source denominator. -/
theorem roof [IsTriangulated C] {X Y : C} (f : T.q.obj X ⟶ T.q.obj Y) :
    ∃ (r : T.Sigma.RightFraction X Y), f = r.map T.q (Localization.inverts _ _) :=
  Localization.exists_rightFraction _ _ f

/-- The manuscript's zero-fraction rule, with a genuine denominator. -/
theorem zero_fraction [IsTriangulated C] {X Y : C} (f : X ⟶ Y) (hf : T.q.map f = 0) :
    ∃ (Z : C) (v : Z ⟶ X), T.Sigma v ∧ v ≫ f = 0 := by
  have he : T.q.map f = T.q.map (0 : X ⟶ Y) := by simpa using hf
  obtain ⟨Z,v,hv,h⟩ := (MorphismProperty.map_eq_iff_precomp T.q T.Sigma f 0).mp he
  exact ⟨Z,v,hv,by simpa using h⟩

variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

instance zeroRetracts : ObjectProperty.IsStableUnderRetracts (IsZero (C := D)) where
  of_retract r h := by
    rw [IsZero.iff_id_eq_zero, ← r.retract, h.eq_of_tgt r.i 0, zero_comp]

instance zeroShift : ObjectProperty.IsStableUnderShift (IsZero (C := D)) ℤ where
  isStableUnderShiftBy n := { le_shift := fun _ h => (shiftFunctor D n).map_isZero h }

instance zeroTriangulated : ObjectProperty.IsTriangulated (IsZero (C := D)) where
  toIsTriangulatedClosed₂ := .mk' (fun U hU h₁ h₃ => U.isZero₂_of_isZero₁₃ hU h₁ h₃)

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  [IsIso (F.map T.first.mor₁)] [IsIso (F.map T.second.mor₁)]

instance kernelRetracts : F.kernel.IsStableUnderRetracts where
  of_retract r h := ObjectProperty.IsStableUnderRetracts.of_retract (P := IsZero (C := D)) (r.map F) h

/-- An exact functor inverting the two displayed arrows kills both
required generating cones, hence their entire thick closure. -/
theorem evaluation_kills : T.S ≤ F.kernel := by
  apply T.thick_minimal F.kernel
  · exact (F.mapTriangle.obj T.first).isZero₃_of_isIso₁
      (F.map_distinguished _ T.first_distinguished)
      (inferInstanceAs (IsIso (F.map T.first.mor₁)))
  · exact (F.mapTriangle.obj T.second).isZero₃_of_isIso₁
      (F.map_distinguished _ T.second_distinguished)
      (inferInstanceAs (IsIso (F.map T.second.mor₁)))

theorem evaluation_inverts : T.Sigma.IsInvertedBy F := by
  intro X Y f hf
  obtain ⟨Z,g,h,hU,hZ⟩ := hf
  exact ((F.mapTriangle.obj (Triangle.mk f g h)).isZero₃_iff_isIso₁
    (F.map_distinguished _ hU)).mp (T.evaluation_kills F _ hZ)

/-- The induced functor from the actual quotient. -/
def evaluation : T.Q ⥤ D := Localization.lift F (T.evaluation_inverts F) T.q

def evaluation_fac : T.q ⋙ T.evaluation F ≅ F :=
  Localization.fac F (T.evaluation_inverts F) T.q

end ConePair
end LittleFinitistic.TwoConeVerdier

end

end OAI

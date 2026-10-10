import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject
namespace LittleFinitistic.FiniteProjectiveHomotopy
universe u v
variable (R : Type u) [Ring R]

/-- Actual bounded complexes of finitely generated projective right/left modules,
according to the chosen scalar ring R. -/
def ComplexProperty (K : CochainComplex (ModuleCat.{v} R) ℤ) : Prop :=
  (∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (K.X i)) ∧
  ∀ i, Module.Finite R (K.X i) ∧ Projective (K.X i)

def objects : ObjectProperty (HomotopyCategory (ModuleCat.{v} R) (.up ℤ)) :=
  fun T => ComplexProperty R T.as

@[simp] theorem objects_quotient (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    objects R ((HomotopyCategory.quotient _ _).obj K) ↔ ComplexProperty R K := Iff.rfl

lemma finite_of_iso {M N : ModuleCat.{v} R} (e : M ≅ N) [Module.Finite R M] : Module.Finite R N :=
  Module.Finite.of_surjective e.toLinearEquiv.toLinearMap e.toLinearEquiv.surjective

lemma finite_biprod (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N] :
    Module.Finite R ((M ⊞ N) : ModuleCat R) :=
  finite_of_iso R (ModuleCat.biprodIsoProd M N).symm

lemma mappingCone_property {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L)
    (hK : ComplexProperty R K) (hL : ComplexProperty R L) :
    ComplexProperty R (CochainComplex.mappingCone f) := by
  obtain ⟨⟨a,b,hbK⟩,hpK⟩ := hK
  obtain ⟨⟨c,d,hbL⟩,hpL⟩ := hL
  constructor
  · refine ⟨min a c - 1,max b d,fun i hi => ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hbK (i+1) (by omega),hbL i (by omega)⟩
  · intro i
    have := (hpK (i+1)).1
    have := (hpK (i+1)).2
    have := (hpL i).1
    have := (hpL i).2
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i+1) rfl
    have := finite_biprod R (K.X (i+1)) (L.X i)
    exact ⟨finite_of_iso R e.symm, Projective.of_iso e.symm inferInstance⟩

lemma finite_projective_of_isZero (M : ModuleCat.{v} R) (h : IsZero M) :
    Module.Finite R M ∧ Projective M := by
  have := ModuleCat.subsingleton_of_isZero h
  exact ⟨inferInstance,h.projective⟩

instance objectsZero : (objects.{u,v} R).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient _ _).obj 0,
    (HomotopyCategory.quotient _ _).map_isZero (isZero_zero _), by
      have hz (i : ℤ) : IsZero ((0 : CochainComplex (ModuleCat.{v} R) ℤ).X i) :=
        (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
      exact ⟨⟨0,0,fun i _ => hz i⟩,fun i => finite_projective_of_isZero R _ (hz i)⟩⟩

instance objectsShift : (objects.{u,v} R).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift T hT := by
        obtain ⟨K,rfl⟩ := T.quotient_obj_surjective
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj]
        change ComplexProperty R (K⟦n⟧)
        obtain ⟨⟨a,b,hb⟩,hp⟩ := hT
        constructor
        · refine ⟨a-n,b-n,fun i hi => ?_⟩
          change IsZero (K.X (i+n))
          exact hb (i+n) (by omega)
        · intro i
          exact hp (i+n) }

instance objectsClosed₃ : (objects.{u,v} R).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as,hf⟩ := (HomotopyCategory.quotient _ _).map_surjective T.mor₁
    refine ⟨(HomotopyCategory.quotient _ _).obj (CochainComplex.mappingCone f),
      mappingCone_property R f h₁ h₂, ⟨?_⟩⟩
    exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (Iso.refl _) (Iso.refl _) (by
        change T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ (HomotopyCategory.quotient _ _).map f
        rw [Category.comp_id,Category.id_comp,hf]))

instance objectsTriangulated : (objects.{u,v} R).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- K^b(proj-R), as a full subcategory with actual bounded f.g. projective representatives. -/
abbrev K := (objects.{u,v} R).FullSubcategory

/-- Its full and faithful inclusion into the ambient homotopy category. -/
abbrev inclusion : K.{u,v} R ⥤ HomotopyCategory (ModuleCat.{v} R) (.up ℤ) := (objects R).ι
end LittleFinitistic.FiniteProjectiveHomotopy

end

end OAI

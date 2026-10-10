import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import OAI.NumberTheory.PiExponent.Geometry.CurveMorphismFinite

namespace OAI

noncomputable section
namespace PiExponent.CurveProperImageDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

theorem genericPoint_map {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (f : C ⟶ Y) [IsDominant f] : f (genericPoint C) = genericPoint Y := by
  have h : IsGenericPoint (f (genericPoint C)) (Set.univ : Set Y) := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec C).image f.continuous
  exact h.eq (genericPoint_spec Y)

theorem target_nongeneric_isClosed {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (f : C ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim C ≤ 1) (y : Y) (hy : y ≠ genericPoint Y) :
    IsClosed ({y} : Set Y) := by
  obtain ⟨c, rfl⟩ := f.surjective y
  have hc : c ≠ genericPoint C := by
    intro heq
    apply hy
    rw [heq, genericPoint_map f]
  simpa only [Set.image_singleton] using f.isClosedMap {c}
    (CurveMorphismFinite.isClosed_singleton_of_ne_genericPoint C hdim c hc)

theorem dimension_eq_one_of_proper_dominant {C Y : Scheme.{u}}
    [IsIntegral C] [IsIntegral Y] [Nontrivial Y]
    (f : C ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim C ≤ 1) : topologicalKrullDim Y = 1 := by
  let : PartialOrder Y := specializationOrder Y
  change Order.krullDim (IrreducibleCloseds Y) = 1
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
  have hle := (Order.krullDim_le_one_iff_forall_isMin (α := Y)).mpr (by
    intro y hy z hzy
    have hclosed := target_nongeneric_isClosed f hdim y hy
    have hz : z ∈ closure ({y} : Set Y) := specializes_iff_mem_closure.mp hzy
    rw [hclosed.closure_eq] at hz
    exact (show z = y from hz).symm.le)
  have hge := (Order.one_le_krullDim_iff (α := Y)).mpr (by
    obtain ⟨y, hy⟩ := exists_ne (⊤ : Y)
    exact ⟨y, ⊤, lt_top_iff_ne_top.mpr hy⟩)
  exact le_antisymm hle hge

theorem image_dimension_eq_one {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) [IsProper f] [IsIntegral f.image] [Nontrivial f.image]
    (hdim : topologicalKrullDim C = 1) : topologicalKrullDim f.image = 1 := by
  have : IsProper (f.toImage ≫ f.imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  let : IsProper f.toImage := IsProper.of_comp f.toImage f.imageι
  exact dimension_eq_one_of_proper_dominant f.toImage hdim.le

theorem image_nontrivial_of_nonconstant {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) (hnonconstant : ¬ ∃ x : X, Set.range f ⊆ {x}) : Nontrivial f.image := by
  classical
  by_contra h
  let : Subsingleton f.image := not_nontrivial_iff_subsingleton.mp h
  apply hnonconstant
  refine ⟨f (genericPoint C), ?_⟩
  rintro _ ⟨c, rfl⟩
  change f c = f (genericPoint C)
  have hc : f.toImage c = f.toImage (genericPoint C) := Subsingleton.elim _ _
  have he := congrArg f.imageι hc
  simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using he

theorem image_dimension_eq_one_of_nonconstant {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) [IsProper f] [IsIntegral f.image]
    (hdim : topologicalKrullDim C = 1)
    (hnonconstant : ¬ ∃ x : X, Set.range f ⊆ {x}) : topologicalKrullDim f.image = 1 := by
  let : Nontrivial f.image := image_nontrivial_of_nonconstant f hnonconstant
  exact image_dimension_eq_one f hdim

end PiExponent.CurveProperImageDimension

end

end OAI

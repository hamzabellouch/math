import OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive
import OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension
import OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

theorem exists_irreducibleClosed_full_dimension (T : Type*) [TopologicalSpace T]
    (n : ℕ) (hdim : topologicalKrullDim T = n) :
    ∃ Z : IrreducibleCloseds T, topologicalKrullDim (Z : Set T) = n := by
  have hdim' : Order.krullDim (IrreducibleCloseds T) = n := hdim
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp (le_of_eq hdim'.symm)
  have hlast : (p.length : ℕ∞) = Order.height p.last := by
    apply le_antisymm (Order.length_le_height_last (p := p))
    have hh := Order.height_le_krullDim p.last
    rw [hdim', ← hp] at hh
    exact_mod_cast hh
  refine ⟨p.last, ?_⟩
  rw [topologicalKrullDim_irreducibleClosed, ← hlast, hp]
  rfl

theorem exists_integral_closed_full_dimension (X : Scheme.{0})
    (n : ℕ) (hdim : topologicalKrullDim X = n) :
    ∃ Y : Scheme.{0}, ∃ i : Y ⟶ X,
      IsClosedImmersion i ∧ IsIntegral Y ∧ topologicalKrullDim Y = n := by
  obtain ⟨Z, hZ⟩ := exists_irreducibleClosed_full_dimension X n hdim
  let C : Closeds X := ⟨Z, Z.isClosed⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have hs : (I.support : Set X) = (Z : Set X) := by
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsReduced I.subscheme := isReduced_vanishingIdeal_subscheme C
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [hs]
    exact Subtype.irreducibleSpace Z.isIrreducible
  refine ⟨I.subscheme, I.subschemeι, inferInstance,
    isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  change topologicalKrullDim (I.support : Set X) = n
  rw [hs]
  exact hZ

variable {X : Scheme.{0}}

theorem ample_section_has_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) (n : ℕ)
    (hdim : topologicalKrullDim X = n) (hn : 0 < n) :
    ∃ y : X, y ∉ sectionOpen X s := by
  by_contra h
  push Not at h
  have : IsIso s := isIso_of_locally_isIso s (by
    intro x
    exact ⟨isoOpen s, h x, isIso_restrict_isoOpen s⟩)
  obtain ⟨C⟩ := nonempty_integralCurve_of_dimension_pos X n hdim hn
  have hpos := curveDegree_pos_of_ample p H hH C
  let e : H.sheaf ≅ structureSheaf X := (asIso s).symm
  have he := eulerCharacteristic_iso (C.embedding ≫ p)
    ((Scheme.Modules.pullback C.embedding).mapIso e ≪≫ pullbackUnitIso C.embedding) 1
  have hz : curveDegree p H C = 0 := by
    unfold curveDegree
    change eulerCharacteristic (C.embedding ≫ p) 1
      ((Scheme.Modules.pullback C.embedding).obj H.sheaf) =
      eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) at he
    rw [he]
    exact sub_self _
  omega

theorem ample_section_zero_nonempty
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) (n : ℕ)
    (hdim : topologicalKrullDim X = n) (hn : 0 < n) :
    Nonempty (zeroIdeal H s).subscheme := by
  obtain ⟨y, hy⟩ := ample_section_has_zero p H hH s n hdim hn
  have hm : y ∈ Set.range (zeroIdeal H s).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, zeroIdeal_support]
    exact hy
  obtain ⟨z, -⟩ := hm
  exact ⟨z⟩

end
end PiExponent.NumericalAmpleness

end OAI

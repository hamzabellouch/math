import OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule

namespace OAI

namespace PiExponentSeshadri.PrincipalSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

lemma scalarEnd_eq_multiply (r : Γ(X,⊤)) : scalarEnd r = IdealModule.multiply r := rfl

lemma end_regular_of_mono (a : O X ⟶ O X) [Mono a] : IsLeftRegular (endValue a) := by
  have hinj : Function.Injective (a.val.app (op ⊤)) :=
    PresheafOfModules.injective_of_mono
      ((Scheme.Modules.toPresheafOfModules X).map a) (op ⊤)
  intro r s hrs
  apply hinj
  change a.app ⊤ r = a.app ⊤ s
  rw [end_apply a ⊤ r, end_apply a ⊤ s]
  change r * endValue a = s * endValue a
  simpa only [mul_comm] using hrs

theorem exact [IsAffine Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (a : O Y ⟶ O Y) [Mono a]
    (h : f.ker.ideal ⟨⊤,isAffineOpen_top Y⟩ = Ideal.span {endValue a}) :
    ∃ hz : a ≫ IdealModule.structureMap f = 0,
      (ShortComplex.mk a (IdealModule.structureMap f) hz).ShortExact := by
  let r := endValue a
  have hr : f.appTop r = 0 := by
    change r ∈ RingHom.ker f.appTop.hom
    erw [← Scheme.Hom.ker_apply f ⟨⊤,isAffineOpen_top Y⟩, h]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hreg : IsLeftRegular r := end_regular_of_mono a
  have hprincipal (U : Y.affineOpens) : f.ker.ideal U =
      Ideal.span {Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r} := by
    rw [← f.ker.map_ideal (U := U) (V := ⟨⊤,isAffineOpen_top Y⟩) (by change U.1 ≤ ⊤; exact le_top), h]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have hi : IsIso (IdealModule.equationToIdeal f r hr) :=
    IdealModule.isIso_equationToIdeal f r hr hprincipal
      (IdealModule.restriction_regular r hreg)
  have he : a = IdealModule.multiply r := by
    rw [← scalarEnd_eq_multiply]
    apply endValue_injective
    simp [r]
  have hz : a ≫ IdealModule.structureMap f = 0 := by
    rw [he]
    exact IdealModule.multiply_structure_zero f r hr
  refine ⟨hz,?_⟩
  let S := ShortComplex.mk a (IdealModule.structureMap f) hz
  let T := ShortComplex.mk (IdealModule.inclusion f) (IdealModule.structureMap f)
    (kernel.condition (IdealModule.structureMap f))
  let e : S ≅ T := ShortComplex.isoMk (@asIso Y.Modules _ _ _ (IdealModule.equationToIdeal f r hr) hi)
    (Iso.refl _) (Iso.refl _) (by
      change IdealModule.equationToIdeal f r hr ≫ IdealModule.inclusion f = a ≫ 𝟙 _
      exact (IdealModule.equationToIdeal_inclusion f r hr).trans
        (he.symm.trans (Category.comp_id a).symm)) (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
  have hg : Epi (IdealModule.structureMap f) := IdealModule.structureMap_epi f
  exact { exact := ShortComplex.exact_of_iso e.symm (ShortComplex.exact_kernel _), epi_g := hg }

end
end PiExponentSeshadri.PrincipalSequence

end OAI

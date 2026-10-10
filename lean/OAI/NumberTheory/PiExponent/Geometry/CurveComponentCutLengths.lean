import OAI.NumberTheory.PiExponent.Approximation.RegularComponentSection
import OAI.NumberTheory.PiExponent.Geometry.CurveComponentLocalLengths
import OAI.NumberTheory.PiExponent.Geometry.CurveComponentZeroPoints
import OAI.NumberTheory.PiExponent.Geometry.CurveCutQuotient

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.SectionZeroStalk

theorem componentLocalCutLength_eq_zero_stalk {X : Scheme.{0}}
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (z : (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hy : (zeroIdeal L s).subschemeι (componentZeroToGlobal L s C z) ∈ U.1) :
    componentLocalCutLength X ((zeroIdeal L s).subschemeι (componentZeroToGlobal L s C z))
      ⟨C,componentZeroToGlobal_mem L s C z⟩
      (sectionGerm L s U e _ hy) =
    Module.length ((zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk z)
      ((zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk z) := by
  let i := reducedComponentι X C
  let J := zeroIdeal (L.pullback i) (pullbackSection i s)
  let y := J.subschemeι z
  let a := sectionGerm L s U e (i y) hy
  obtain ⟨eF,heF⟩ := exists_pullback_frame_sectionGerm i L s U e
  let V : (reducedComponent X C).affineOpens := ⟨i ⁻¹ᵁ U.1,U.2.preimage i⟩
  let b := sectionGerm (L.pullback i) (pullbackSection i s) V eF y hy
  have hb : b = i.stalkMap y a := heF y hy
  have hcut := reducedComponent_cut_length X C y a
  change componentLocalCutLength X (i y) ⟨C,reducedComponentι_mem X C y⟩ a =
    Module.length (J.subscheme.presheaf.stalk z) (J.subscheme.presheaf.stalk z)
  change Module.length (X.presheaf.stalk (i y))
    ((X.presheaf.stalk (i y)) ⧸ ((reducedComponentStalkPrime X C y).val ⊔ Ideal.span {a})) = _
  rw [hcut,← hb]
  have hsc : Module.length ((reducedComponent X C).presheaf.stalk y)
      (((reducedComponent X C).presheaf.stalk y) ⧸ Ideal.span {b}) =
    Module.length (((reducedComponent X C).presheaf.stalk y) ⧸ Ideal.span {b})
      (((reducedComponent X C).presheaf.stalk y) ⧸ Ideal.span {b}) :=
    Module.length_eq_of_surjective (M := ((reducedComponent X C).presheaf.stalk y) ⧸
      Ideal.span {b}) Ideal.Quotient.mk_surjective
  exact hsc.trans (intrinsic_length_eq_of_ringEquiv
    (zeroStalkQuotientEquiv (L.pullback i) (pullbackSection i s) V eF z hy))

theorem componentLocalCutLength_eq_zero_stalk_at {X : Scheme.{0}}
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (t : {y : (zeroIdeal L s).subscheme // (zeroIdeal L s).subschemeι y ∈ C.val})
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hy : (zeroIdeal L s).subschemeι t.val ∈ U.1) :
    componentLocalCutLength X ((zeroIdeal L s).subschemeι t.val) ⟨C,t.property⟩
      (sectionGerm L s U e _ hy) =
    Module.length ((zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk
        ((componentZeroPointEquiv L s C).symm t))
      ((zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk
          ((componentZeroPointEquiv L s C).symm t)) := by
  obtain ⟨z,rfl⟩ := (componentZeroPointEquiv L s C).surjective t
  exact (componentLocalCutLength_eq_zero_stalk L s C z U e hy).trans
    (congrArg (fun w : (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme =>
      Module.length ((zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk w)
        ((zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk w))
      ((componentZeroPointEquiv L s C).symm_apply_apply z)).symm

end
end PiExponent.CurveCycle

end OAI

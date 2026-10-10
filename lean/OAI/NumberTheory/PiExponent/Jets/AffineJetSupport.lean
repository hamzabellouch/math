import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity
import OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula
import OAI.NumberTheory.PiExponent.Approximation.TwistSections

namespace OAI

noncomputable section
namespace PiExponent.AffineJetSupport
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity
variable {X Y : Scheme}

private theorem map_bijective_of_eq {T : Type*} [Category T] [Quiver.IsThin T]
    (F : Tᵒᵖ ⥤ AddCommGrpCat) {U V : T}
    (h : U = V) (i : U ⟶ V) : Function.Bijective (F.map i.op) := by
  subst V
  have hi : i = 𝟙 U := Subsingleton.elim _ _
  subst i
  rw [op_id]
  erw [F.map_id]
  exact Function.bijective_id

theorem restriction_surjective_of_iso {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (h : Function.Surjective (N.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) :
    Function.Surjective (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) := by
  intro s
  obtain ⟨t, ht⟩ := h (e.hom.app U s)
  obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).surjective t
  refine ⟨r, (ConcreteCategory.bijective_of_isIso (e.hom.app U)).injective ?_⟩
  have hn := CategoryTheory.congr_fun
    (e.hom.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op) r
  change e.hom.app U (M.presheaf.map _ r) = N.presheaf.map _ (e.hom.app ⊤ r) at hn
  rw [hn, hr, ht]

theorem pushforward_restriction_bijective (f : Y ⟶ X) (M : Y.Modules) (U : X.Opens)
    (hU : f ⁻¹ᵁ U = ⊤) :
    Function.Bijective (((Scheme.Modules.pushforward f).obj M).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op) := by
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  have he : f ⁻¹ᵁ U = f ⁻¹ᵁ (⊤ : X.Opens) := by simp [hU]
  exact map_bijective_of_eq M.presheaf he _

theorem subscheme_preimage_eq_top (I : X.IdealSheafData) (U : X.Opens)
    (hs : (I.support : Set X) ⊆ U) : I.subschemeι ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro x hx
  apply hs
  rw [← I.range_subschemeι]
  exact ⟨x, rfl⟩

theorem twistedQuotient_restriction_surjective (I : X.IdealSheafData)
    (A : LineBundle X) (n : ℕ) (U : X.Opens)
    (hs : (I.support : Set X) ⊆ U) :
    Function.Surjective (((moduleTwistFunctor A n).obj (jetQuotient I)).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op) := by
  apply restriction_surjective_of_iso
    (ProjectionFormula.twistIso I.subschemeι (PiExponentSeshadri.IdealModule.unit I.subscheme) A n).symm U
  exact (pushforward_restriction_bijective I.subschemeι _ U
    (subscheme_preimage_eq_top I U hs)).surjective

def restrictionSectionsIso (M : X.Modules) (U : X.Opens) :
    Γ(M.restrict U.ι, ⊤) ≅ Γ(M,U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

def sectionsIso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) : Γ(M,U) ≅ Γ(N,U) :=
  ((Scheme.Modules.toPresheaf X).mapIso e).app (op U)

def localQuotientEquiv (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    Γ((moduleTwistFunctor A n).obj (jetQuotient I), U.1) ≃
      (Γ(X,U.1) ⧸ I.ideal U) :=
  (restrictionSectionsIso ((moduleTwistFunctor A n).obj (jetQuotient I)) U.1).symm.addCommGroupIsoToAddEquiv.toEquiv |>.trans
    ((sectionsIso ((moduleTwistRestrictFrame A U.1 e n).app (jetQuotient I)) ⊤).addCommGroupIsoToAddEquiv.toEquiv.trans
      ((restrictionSectionsIso (jetQuotient I) U.1).addCommGroupIsoToAddEquiv.toEquiv.trans
        (I.subschemeObjIso U).commRingCatIsoToRingEquiv.toEquiv))

def globalQuotientValue (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X ((moduleTwistFunctor A n).obj (jetQuotient I))) :
    Γ(X,U.1) ⧸ I.ideal U :=
  localQuotientEquiv I A n U e
    (((moduleTwistFunctor A n).obj (jetQuotient I)).presheaf.map
      (homOfLE (le_top : U.1 ≤ ⊤)).op
      (moduleSectionEquiv ((moduleTwistFunctor A n).obj (jetQuotient I)) s))

theorem globalQuotientValue_surjective (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (hs : (I.support : Set X) ⊆ U.1) :
    Function.Surjective (globalQuotientValue I A n U e) :=
  (localQuotientEquiv I A n U e).surjective.comp
    ((twistedQuotient_restriction_surjective I A n U.1 hs).comp
      (moduleSectionEquiv ((moduleTwistFunctor A n).obj (jetQuotient I))).surjective)

end PiExponent.AffineJetSupport
end

end OAI

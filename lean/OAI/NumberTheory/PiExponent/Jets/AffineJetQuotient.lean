import OAI.NumberTheory.PiExponent.Jets.AffineJetSupport

namespace OAI

noncomputable section
namespace PiExponent.AffineJetQuotient
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity PiExponent.AffineJetSupport
variable {X : Scheme}

@[reassoc] theorem restrictionSectionsIso_natural {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) :
    ((Scheme.Modules.restrictFunctor U.ι).map f).app ⊤ ≫
        (restrictionSectionsIso N U).hom =
      (restrictionSectionsIso M U).hom ≫ f.app U := by
  change f.app (U.ι ''ᵁ ⊤) ≫ N.presheaf.map (eqToHom U.ι_image_top.symm).op =
    M.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ f.app U
  exact (f.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op).symm

def untwistSectionsIso (A : LineBundle X) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) (M : X.Modules) :
    Γ((moduleTwistFunctor A n).obj M,U) ≅ Γ(M,U) :=
  (restrictionSectionsIso ((moduleTwistFunctor A n).obj M) U).symm ≪≫
    sectionsIso ((moduleTwistRestrictFrame A U e n).app M) ⊤ ≪≫
    restrictionSectionsIso M U

@[reassoc] theorem untwistSectionsIso_natural (A : LineBundle X) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ)
    {M N : X.Modules} (f : M ⟶ N) :
    ((moduleTwistFunctor A n).map f).app U ≫ (untwistSectionsIso A U e n N).hom =
      (untwistSectionsIso A U e n M).hom ≫ f.app U := by
  have hn := congrArg (fun g => g.app ⊤)
    ((moduleTwistRestrictFrame A U e n).hom.naturality f)
  simp only [Scheme.Modules.Hom.comp_app] at hn
  change ((Scheme.Modules.restrictFunctor U.ι).map ((moduleTwistFunctor A n).map f)).app ⊤ ≫
      ((moduleTwistRestrictFrame A U e n).app N).hom.app ⊤ =
    ((moduleTwistRestrictFrame A U e n).app M).hom.app ⊤ ≫
      ((Scheme.Modules.restrictFunctor U.ι).map f).app ⊤ at hn
  apply (cancel_epi (restrictionSectionsIso ((moduleTwistFunctor A n).obj M) U).hom).mp
  simp only [untwistSectionsIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← restrictionSectionsIso_natural_assoc]
  simp only [Iso.hom_inv_id_assoc]
  change _ ≫ ((moduleTwistRestrictFrame A U e n).app N).hom.app ⊤ ≫ _ = _
  rw [← Category.assoc, hn, Category.assoc, restrictionSectionsIso_natural]
  rfl

theorem localQuotientEquiv_apply (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : Γ((moduleTwistFunctor A n).obj (jetQuotient I),U.1)) :
    localQuotientEquiv I A n U e s =
      (I.subschemeObjIso U).hom ((untwistSectionsIso A U.1 e n (jetQuotient I)).hom s) := rfl

def globalSectionCoefficient (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) : Γ(X,U.1) :=
  (untwistSectionsIso A U.1 e n (structureSheaf X)).hom
    ((s ≫ (moduleTwistUnitIso A n).inv).app U.1 (1 : Γ(X,U.1)))

theorem globalQuotientValue_jetRestriction (I : X.IdealSheafData)
    (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    globalQuotientValue (I^n) A n U e (jetRestriction I A n s) =
      Ideal.Quotient.mk ((I^n).ideal U) (globalSectionCoefficient A n U e s) := by
  unfold globalQuotientValue
  erw [moduleSectionEquiv_apply, section_value_natural, localQuotientEquiv_apply]
  let q := PiExponentSeshadri.IdealModule.structureMap (I^n).subschemeι
  let t := s ≫ (moduleTwistUnitIso A n).inv
  change ((I^n).subschemeObjIso U).hom
    ((untwistSectionsIso A U.1 e n (jetQuotient (I^n))).hom
      (((moduleTwistFunctor A n).map q).app U.1 (t.app U.1 (1 : Γ(X,U.1))))) = _
  have hn := CategoryTheory.congr_fun (untwistSectionsIso_natural A U.1 e n q)
    (t.app U.1 (1 : Γ(X,U.1)))
  change (untwistSectionsIso A U.1 e n (jetQuotient (I^n))).hom
      (((moduleTwistFunctor A n).map q).app U.1 (t.app U.1 (1 : Γ(X,U.1)))) =
    q.app U.1 ((untwistSectionsIso A U.1 e n (structureSheaf X)).hom (t.app U.1 (1 : Γ(X,U.1)))) at hn
  rw [hn]
  change ((I^n).subschemeObjIso U).hom
    ((I^n).subschemeι.app U.1 (globalSectionCoefficient A n U e s)) = _
  rw [Scheme.IdealSheafData.subschemeι_app]
  exact ((I^n).subschemeObjIso U).inv_hom_id_apply _

theorem coefficient_quotient_surjective_of_jetRestriction
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (hs : ((I^n).support : Set X) ⊆ U.1)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : GlobalSections X (modulePow X A.sheaf n) =>
      Ideal.Quotient.mk ((I^n).ideal U) (globalSectionCoefficient A n U e s)) := by
  intro q
  obtain ⟨t, ht⟩ := globalQuotientValue_surjective (I^n) A n U e hs q
  obtain ⟨s, rfl⟩ := hjet t
  exact ⟨s, (globalQuotientValue_jetRestriction I A n U e s).symm.trans ht⟩

end PiExponent.AffineJetQuotient
end

end OAI

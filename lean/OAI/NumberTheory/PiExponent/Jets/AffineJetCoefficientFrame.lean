import OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial

namespace OAI

noncomputable section
namespace PiExponent.AffineJetCoefficientFrame
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.AffineJetSupport PiExponent.AffineJetQuotient
variable {X : Scheme}

def untwistPowerFrame (A : LineBundle X) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) :
    (modulePow X A.sheaf n).restrict U.ι ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTwistUnitIso A n).symm ≪≫
    (moduleTwistRestrictFrame A U e n).app (structureSheaf X) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

lemma restrictionSectionsIso_restrict_value {M : X.Modules}
    (s : O X ⟶ M) (U : X.Opens) :
    (restrictionSectionsIso M U).inv (s.app U (1 : Γ(X,U))) =
      (restrictSection U.ι s).app ⊤ (1 : Γ(U.toScheme,⊤)) := by
  have h : (restrictionSectionsIso M U).hom
      ((restrictSection U.ι s).app ⊤ (1 : Γ(U.toScheme,⊤))) =
      s.app U (1 : Γ(X,U)) := openSectionEquiv_restrict s U
  rw [← h]
  exact (restrictionSectionsIso M U).hom_inv_id_apply _

lemma restrictionSectionsIso_unit (U : X.Opens)
    (t : Γ((structureSheaf X).restrict U.ι,⊤)) :
    (restrictionSectionsIso (structureSheaf X) U).hom t =
      U.topIso.hom ((Scheme.Modules.restrictUnitIso U.ι).hom.app ⊤ t) := by
  change U.topIso.hom t = U.topIso.hom ((U.ι.appIso ⊤).hom t)
  rw [U.ι_appIso]
  rfl

theorem globalSectionCoefficient_eq (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    globalSectionCoefficient A n U e s =
      U.1.topIso.hom (coefficient (untwistPowerFrame A U.1 e n)
        (restrictSection U.1.ι s)) := by
  change (restrictionSectionsIso (structureSheaf X) U.1).hom
      (((moduleTwistRestrictFrame A U.1 e n).app (structureSheaf X)).hom.app ⊤
        ((restrictionSectionsIso ((moduleTwistFunctor A n).obj (structureSheaf X)) U.1).inv
          ((s ≫ (moduleTwistUnitIso A n).inv).app U.1 (1 : Γ(X,U.1))))) =
    U.1.topIso.hom ((Scheme.Modules.restrictUnitIso U.1.ι).hom.app ⊤
      (((moduleTwistRestrictFrame A U.1 e n).app (structureSheaf X)).hom.app ⊤
        ((restrictSection U.1.ι (s ≫ (moduleTwistUnitIso A n).inv)).app ⊤
          (1 : Γ(U.1.toScheme,⊤)))))
  exact (congrArg (fun t => (restrictionSectionsIso (structureSheaf X) U.1).hom
      (((moduleTwistRestrictFrame A U.1 e n).app (structureSheaf X)).hom.app ⊤ t))
    (restrictionSectionsIso_restrict_value (s ≫ (moduleTwistUnitIso A n).inv) U.1)).trans
      (restrictionSectionsIso_unit U.1 _)

open PiExponent.ExceptionalAffineChart PiExponent.AffineJetPolynomial
variable {R : Type} [CommRing R]

def polynomialPowerFrame (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (n : ℕ)
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme) :
    (modulePow X A.sheaf n).restrict j ≅ O (Spec (CommRingCat.of R)) :=
  (Scheme.Modules.restrictFunctorCongr j.isoOpensRange_hom_ι.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).app _ ≪≫
    restrictFrame j.isoOpensRange.hom (untwistPowerFrame A (chartOpen j).1 e n)

theorem polynomialCoefficient_eq (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (n : ℕ)
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    polynomialCoefficient j A n e s =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom
        (coefficient (polynomialPowerFrame j A n e) (restrictSection j s)) := by
  have hframe : coefficient (polynomialPowerFrame j A n e) (restrictSection j s) =
      j.isoOpensRange.hom.appTop (coefficient (untwistPowerFrame A (chartOpen j).1 e n)
        (restrictSection (chartOpen j).1.ι s)) := by
    rw [polynomialPowerFrame, coefficient_transport]
    exact (congrArg (coefficient
      ((Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).app
        (modulePow X A.sheaf n) ≪≫
          restrictFrame j.isoOpensRange.hom (untwistPowerFrame A (chartOpen j).1 e n)))
      (restrictSection_congr j.isoOpensRange_hom_ι.symm s)).trans
        (coefficient_restrict_comp j.isoOpensRange.hom j.opensRange.ι _ s)
  unfold polynomialCoefficient
  rw [globalSectionCoefficient_eq]
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (j.isoOpensRange.hom.appTop ((chartOpen j).1.topIso.inv
        ((chartOpen j).1.topIso.hom _))) = _
  rw [(chartOpen j).1.topIso.hom_inv_id_apply]
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom hframe.symm

end PiExponent.AffineJetCoefficientFrame
end

end OAI

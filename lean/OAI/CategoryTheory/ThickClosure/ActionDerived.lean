import OAI.CategoryTheory.ThickClosure.LaurentAction

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.LaurentDg
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u w
variable {R : Type u} [Ring R] {D : ℕ}

noncomputable def actualEquivalence (hD : 0 < D) : Module R D ≌ ActionModule R D := by
  letI : (actionFunctor (R:=R) (D:=D)).EssSurj := actionFunctor_essSurj hD
  letI : (actionFunctor (R:=R) (D:=D)).IsEquivalence := {}
  exact (actionFunctor (R:=R) (D:=D)).asEquivalence

namespace ActionModule
def forget : ActionModule R D ⥤ ChainComplex (ModuleCat.{u} R) ℤ where
  obj G := ChainComplex.of G.X G.d G.dd
  map f := ChainComplex.ofHom f.f (by intro n; simpa only [ChainComplex.of_d] using f.comm_d n)
  map_id G := by ext n; rfl
  map_comp f g := by ext n; rfl

def quasiIso : MorphismProperty (ActionModule R D) := fun _ _ f => QuasiIso (forget.map f)

def homology (n : ℤ) : ActionModule R D ⥤ ModuleCat.{u} R :=
  forget ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down ℤ) n

variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]
abbrev localization (hD : 0 < D) : ActionModule R D ⥤ LaurentDg.Derived R D :=
  (actualEquivalence hD).inverse ⋙ LaurentDg.localization R D
end ActionModule
noncomputable def actionForgetIso :
    actionFunctor (R:=R) (D:=D) ⋙ ActionModule.forget ≅ LaurentDg.forget :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro M N f; simp; rfl)

noncomputable def inverseForgetIso (hD : 0 < D) :
    (actualEquivalence (R:=R) hD).inverse ⋙ LaurentDg.forget ≅ ActionModule.forget :=
  Functor.isoWhiskerLeft (actualEquivalence hD).inverse actionForgetIso.symm ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (actualEquivalence hD).counitIso ActionModule.forget ≪≫
  Functor.leftUnitor ActionModule.forget

lemma inverse_quasiIso_iff (hD : 0 < D) {M N : ActionModule R D} (f : M ⟶ N) :
    LaurentDg.quasiIso ((actualEquivalence hD).inverse.map f) ↔ ActionModule.quasiIso f := by
  change QuasiIso (LaurentDg.forget.map ((actualEquivalence hD).inverse.map f)) ↔
    QuasiIso (ActionModule.forget.map f)
  rw [_root_.quasiIso_iff, _root_.quasiIso_iff]
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  apply forall_congr'
  intro n
  exact NatIso.isIso_map_iff (Functor.isoWhiskerRight (inverseForgetIso hD)
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down ℤ) n)) f

namespace ActionModule
variable (R) (D) (hD : 0 < D)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

theorem localization_isLocalization :
    (localization (R:=R) hD).IsLocalization (quasiIso (R:=R) (D:=D)) := by
  let := LaurentDg.localization_isLocalization R D
  apply Functor.IsLocalization.of_equivalence_source (LaurentDg.localization R D)
    (LaurentDg.quasiIso (R:=R) (D:=D)) (localization (R:=R) hD)
    (quasiIso (R:=R) (D:=D)) (actualEquivalence hD)
  · intro M N f hf
    apply MorphismProperty.le_isoClosure
    change QuasiIso (forget.map (actionFunctor.map f))
    rw [_root_.quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso (((actionFunctor ⋙ forget) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down ℤ) n).map f)
    rw [NatIso.isIso_map_iff (Functor.isoWhiskerRight actionForgetIso _)]
    have : QuasiIso (LaurentDg.forget.map f) := hf
    exact inferInstanceAs (IsIso (homologyMap (LaurentDg.forget.map f) n))
  · intro M N f hf
    exact Localization.inverts (LaurentDg.localization R D) (LaurentDg.quasiIso (R:=R) (D:=D))
      ((actualEquivalence hD).inverse.map f) ((inverse_quasiIso_iff hD f).mpr hf)
  · exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (actualEquivalence hD).unitIso.symm (LaurentDg.localization R D) ≪≫
      Functor.leftUnitor (LaurentDg.localization R D)

noncomputable def localizationHomologyIso (n : ℤ) :
    localization (R:=R) hD ⋙ LaurentDg.derivedHomology n ≅ homology (R:=R) (D:=D) n :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (actualEquivalence hD).inverse
    (LaurentDg.localizationHomologyIso n) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (inverseForgetIso hD) _
end ActionModule
end HahnWilson.LaurentDg

end

end OAI

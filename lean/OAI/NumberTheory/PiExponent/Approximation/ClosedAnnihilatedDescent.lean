import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {R S : CommRingCat.{0}}

def specPushforwardSectionsIso (φ : R ⟶ S) (N : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N) ≅
      (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj N) := by
  let E : TopCat.Sheaf (ModuleCat R) (Spec R) ⥤ ModuleCat R :=
    TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)
  exact E.mapIso ((pushforwardCompModulesSpecToSheafIso φ).app N)

def specPushforwardTildeIso (φ : R ⟶ S) (N : ModuleCat S) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj N) := by
  let P := (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)
  let : IsIso P.fromTildeΓ := isIso_fromTildeΓ_pushforward φ (tilde N)
  exact (asIso P.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso
    (specPushforwardSectionsIso φ (tilde N) ≪≫
      (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop N).symm)

def quotientModule (I : Ideal R) (M : ModuleCat R)
    (h : I ≤ Module.annihilator R M) : ModuleCat (CommRingCat.of (R ⧸ I)) := by
  let ht : Module.IsTorsionBySet R M I := fun {x} {a} =>
    Module.mem_annihilator.mp (h a.property) x
  letI := ht.module
  exact ModuleCat.of _ M

def quotientModuleRestrictIso (I : Ideal R) (M : ModuleCat R)
    (h : I ≤ Module.annihilator R M) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (quotientModule I M h) ≅ M :=
  Iso.refl M

def affineDescent (I : Ideal R) (M : (Spec R).Modules)
    (h : I ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Spec (CommRingCat.of (R ⧸ I))).Modules :=
  tilde (quotientModule I (moduleSpecΓFunctor.obj M) h)

instance affineDescent_isQuasicoherent (I : Ideal R) (M : (Spec R).Modules)
    (h : I ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (affineDescent I M h).IsQuasicoherent := by
  unfold affineDescent
  infer_instance

def affineDescentPushforwardIso (I : Ideal R) (M : (Spec R).Modules) [M.IsQuasicoherent]
    (h : I ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
      (affineDescent I M h) ≅ M :=
  specPushforwardTildeIso _ _ ≪≫
    (tilde.functor R).mapIso (quotientModuleRestrictIso I (moduleSpecΓFunctor.obj M) h) ≪≫
      @asIso _ _ _ _ M.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M)

instance quotientModule_finite (I : Ideal R) (M : ModuleCat R) [Module.Finite R M]
    (h : I ≤ Module.annihilator R M) :
    Module.Finite (CommRingCat.of (R ⧸ I)) (quotientModule I M h) := by
  let ht : Module.IsTorsionBySet R M I := fun {x} {a} =>
    Module.mem_annihilator.mp (h a.property) x
  let := ht.module
  let : IsScalarTower R (R ⧸ I) M := ht.isScalarTower
  change Module.Finite (R ⧸ I) M
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

lemma affineDescent_finitePresentation [IsNoetherianRing R] (I : Ideal R)
    (M : (Spec R).Modules) [Module.Finite R (moduleSpecΓFunctor.obj M)]
    (h : I ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (affineDescent I M h).IsFinitePresentation :=
  PiExponent.FiniteGlobalPresentation.tilde_finitePresentation _

theorem exists_affine_coherent_descent [IsNoetherianRing R] (I : Ideal R)
    (M : (Spec R).Modules) [M.IsFinitePresentation]
    (h : I ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    ∃ N : (Spec (CommRingCat.of (R ⧸ I))).Modules,
      N.IsFinitePresentation ∧ Nonempty
        ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj N ≅ M) := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    PiExponent.CoherentAffineFinite.spec_sections_finite_of_localGenerators M
      (PiExponent.CoherentAffineFinite.locallyFinitelyGenerated_of_finitePresentation M)
  exact ⟨affineDescent I M h, affineDescent_finitePresentation I M h,
    ⟨affineDescentPushforwardIso I M h⟩⟩

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI

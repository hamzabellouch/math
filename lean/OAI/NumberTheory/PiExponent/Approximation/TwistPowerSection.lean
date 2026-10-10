import OAI.NumberTheory.PiExponent.Approximation.TensorMixedSection
import OAI.NumberTheory.PiExponent.Approximation.TwistSectionScalars

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma moduleTensorComm_pure (M N : X.Modules) (U : X.Opens)
    (m : Γ(M,U)) (n : Γ(N,U)) :
    (moduleTensorComm M N).hom.app U (pure M N U m n) = pure N M U n m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  have h := (adj X).unit.naturality (β_ M.val N.val).hom
  exact (congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] n)) h).symm

theorem moduleTwistSection_unitIso (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    (moduleTwistSection L s n).app (structureSheaf X) ≫ (moduleTwistUnitIso L n).hom =
      powerSection s n := by
  induction n with
  | zero =>
    simp [moduleTwistSection, moduleTwistUnitIso, powerSection_zero]
    exact Category.id_comp _
  | succ n ih =>
    apply (moduleSectionEquiv (modulePow X L.sheaf (n+1))).injective
    change (moduleTensorComm (modulePow X L.sheaf n) L.sheaf).hom.app ⊤
      ((moduleTensorMap (moduleTwistUnitIso L n).hom (𝟙 L.sheaf)).app ⊤
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj (structureSheaf X)) s).app ⊤
          (((moduleTwistSection L s n).app (structureSheaf X)).app ⊤ (1 : Γ(X,⊤))))) =
      (powerSection s (n+1)).app ⊤ (1 : Γ(X,⊤))
    let v := ((moduleTwistSection L s n).app (structureSheaf X)).app ⊤ (1 : Γ(X,⊤))
    have hm := congrArg (fun z => (moduleTensorComm (modulePow X L.sheaf n) L.sheaf).hom.app ⊤
      ((moduleTensorMap (moduleTwistUnitIso L n).hom (𝟙 L.sheaf)).app ⊤ z))
      (moduleSectionMultiplyRight_pure ((moduleTwistFunctor L n).obj (structureSheaf X)) s ⊤ v)
    have ht := congrArg (fun z => (moduleTensorComm (modulePow X L.sheaf n) L.sheaf).hom.app ⊤ z)
      (TensorPure.map_pure (moduleTwistUnitIso L n).hom (𝟙 L.sheaf) ⊤ v
        (s.app ⊤ (1 : Γ(X,⊤))))
    have hc := moduleTensorComm_pure (modulePow X L.sheaf n) L.sheaf ⊤
      ((moduleTwistUnitIso L n).hom.app ⊤ v) (s.app ⊤ (1 : Γ(X,⊤)))
    refine hm.trans (ht.trans (hc.trans (Eq.trans ?_ (power_succ_apply s n ⊤).symm)))
    have hi := congrArg (fun f : structureSheaf X ⟶ modulePow X L.sheaf n =>
      f.app ⊤ (1 : Γ(X,⊤))) ih
    change (moduleTwistUnitIso L n).hom.app ⊤
      (((moduleTwistSection L s n).app (structureSheaf X)).app ⊤ (1 : Γ(X,⊤))) =
      (powerSection s n).app ⊤ (1 : Γ(X,⊤)) at hi
    exact congrArg (fun z => pure L.sheaf (modulePow X L.sheaf n) ⊤
      (s.app ⊤ (1 : Γ(X,⊤))) z) hi

lemma moduleTwistSection_unitIso_app (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) (U : X.Opens) (a : Γ(X,U)) :
    (moduleTwistUnitIso L n).hom.app U
      (((moduleTwistSection L s n).app (structureSheaf X)).app U a) =
      (powerSection s n).app U a :=
  congrArg (fun f : structureSheaf X ⟶ modulePow X L.sheaf n => f.app U a)
    (moduleTwistSection_unitIso L s n)

end
end PiExponentSeshadri.Geometry

end OAI

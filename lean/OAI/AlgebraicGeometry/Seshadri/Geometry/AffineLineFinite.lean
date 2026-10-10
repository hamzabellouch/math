import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PowerExtension
import OAI.AlgebraicGeometry.Seshadri.Sheaves.LineBundleCoherent

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

lemma finite_sections_of_frame {X : Scheme.{0}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) : Module.Finite Γ(X,U) Γ(M,U) := by
  let e' : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) := overFrame e
  let j : Over U := Over.mk (𝟙 U)
  let f : Γ(X,U) →ₗ[Γ(X,U)] Γ(M,U) := (e'.inv.val.app (op j)).hom
  have hf : Function.Surjective f := (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation (X.ringCatSheaf.over U) (op j)).mapIso e').inv).surjective
  exact Module.Finite.of_surjective f hf

theorem LineBundle.spec_sections_finite {R : CommRingCat.{0}} (L : LineBundle (Spec R)) :
    Module.Finite R ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op ⊤)) := by
  classical
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let t : Set R := {r | Nonempty (L.sheaf.restrict (D r).ι ≅
    structureSheaf (D r).toScheme)}
  have ht : Ideal.span t = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x hx
    obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
    obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hxr,hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr
      ⟨⟨MaximalSeshadri.InvertibleLocal.frameOfLE L.sheaf hrU e⟩,hxr⟩⟩
  let M := ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op ⊤))
  let (r : t) : Module R Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| Module R
      ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op (PrimeSpectrum.basicOpen r.val)))
  let (r : t) : Module Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    (L.sheaf.val.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : Algebra R Γ(Spec R, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| Algebra R
      ((Spec.structureSheaf R).presheaf.obj (op (PrimeSpectrum.basicOpen r.val)))
  have (r : t) : IsLocalization.Away r.val Γ(Spec R, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| IsLocalization.Away r.val
      ((Spec.structureSheaf R).presheaf.obj (op (PrimeSpectrum.basicOpen r.val)))
  have (r : t) : IsScalarTower R Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    IsScalarTower.of_compHom R Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val)
  let f (r : t) : M →ₗ[R] Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    ((modulesSpecToSheaf.obj L.sheaf).obj.map (homOfLE le_top).op).hom
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing L.sheaf).mp inferInstance
  have (r : t) : IsLocalizedModule.Away r.val (f r) := hloc r.val
  have hfin (r : t) : Module.Finite Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    finite_sections_of_frame L.sheaf _ r.property.some
  exact Module.Finite.of_localizationSpan' t ht f hfin

end
end MaximalSeshadri.Geometry
end


end
end

end OAI

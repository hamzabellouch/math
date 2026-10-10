import OAI.NumberTheory.PiExponent.Approximation.FrameSections
import OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension
import OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.noetherian_power_extension [NoetherianSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (f : Γ(X,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) := by
  have : (structureSheaf X).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  have : (structureSheaf X).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (structureSheaf X)).choose.isQuasicoherent
  obtain ⟨N, hN⟩ := PiExponent.TwistGlobalExtension.global_twist_extension_native L s
    (structureSheaf X) f
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN n hn
  let P := (moduleTwistFunctor L n).obj (structureSheaf X)
  let Q := modulePow X L.sheaf n
  let D := sectionOpen X s
  let e := moduleTwistUnitIso L n
  let t : GlobalSections X Q := (moduleSectionEquiv Q).symm (e.hom.app ⊤ z)
  refine ⟨t, ?_⟩
  have htop : t.app ⊤ (1 : Γ(X,⊤)) = e.hom.app ⊤ z :=
    (moduleSectionEquiv Q).apply_symm_apply _
  have ht : Q.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op
      (e.hom.app ⊤ z) = t.app D (1 : Γ(X,D)) :=
    (congrArg (fun x : Γ(Q,⊤) =>
      Q.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op x) htop).symm.trans
        (section_value_natural t (homOfLE (show D ≤ ⊤ from le_top)))
  have he := CategoryTheory.congr_fun
    (e.hom.mapPresheaf.naturality (homOfLE (show D ≤ ⊤ from le_top)).op) z
  change e.hom.app D (P.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op z) =
    Q.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op (e.hom.app ⊤ z) at he
  have hp := moduleTwistSection_unitIso_app L s n D f
  calc
    t.app D (1 : Γ(X,D)) =
        Q.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op (e.hom.app ⊤ z) := ht.symm
    _ = e.hom.app D (P.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op z) := he.symm
    _ = e.hom.app D (((moduleTwistSection L s n).app (structureSheaf X)).app D f) :=
      congrArg (fun x => e.hom.app D x) hz
    _ = (powerSection s n).app D f := hp
    _ = f • (powerSection s n).app D (1 : Γ(X,D)) := by
      have hm := (powerSection s n).app_smul (r := f) (x := (1 : Γ(X,D)))
      change (powerSection s n).app D (show Γ(X,D) from f * 1) = _ at hm
      exact (congrArg ((powerSection s n).app D) (mul_one f)).symm.trans hm

theorem LineBundle.noetherian_power_extension_ratio [NoetherianSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (f : Γ((sectionOpen X s).toScheme,⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      restrictSection (sectionOpen X s).ι t = scalarEnd f ≫
        restrictSection (sectionOpen X s).ι (powerSection s n) := by
  obtain ⟨N, hN⟩ := L.noetherian_power_extension s ((sectionOpen X s).topIso.hom f)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨t, ht⟩ := hN n hn
  refine ⟨t, ?_⟩
  apply (openSectionEquiv (modulePow X L.sheaf n) (sectionOpen X s)).injective
  erw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict]
  exact ht

end
end PiExponentSeshadri.Geometry

end OAI

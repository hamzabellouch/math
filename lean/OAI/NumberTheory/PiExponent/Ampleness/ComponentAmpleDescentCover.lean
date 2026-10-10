import OAI.NumberTheory.PiExponent.Ampleness.AmpleGeneratedTensor
import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open _root_.OAI.PiExponentSeshadri.Geometry
variable {X Y Z : Scheme.{0}}

def pullbackTwistIso (f : Y ⟶ X) (K L : LineBundle X) (n : ℕ) :
    ((K.tensor (L.pow n)).pullback f).sheaf ≅
      (moduleTwistFunctor (L.pullback f) n).obj (K.pullback f).sheaf :=
  PullbackTensor.iso f K (L.pow n) ≪≫
    moduleTensorIso (Iso.refl _) (PullbackTensor.powIso f L n) ≪≫
    (moduleTwistPowerIso (L.pullback f) (K.pullback f).sheaf n).symm

theorem eventual_pullback_twist_sections [NoetherianSpace Y]
    (f : Y ⟶ X) (K L : LineBundle X) (hL : (L.pullback f).IsAmple) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ y : Y,
      ∃ s : GlobalSections Y ((K.tensor (L.pow n)).pullback f).sheaf,
        y ∈ sectionOpen Y s := by
  have : (K.pullback f).sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation _
  obtain ⟨N,hN⟩ := PiExponent.AmpleGlobalGeneration.ample_eventual_global_generators
    (L.pullback f) hL (K.pullback f).sheaf
  refine ⟨N, fun n hn y => ?_⟩
  obtain ⟨G,hG⟩ := hN n hn
  let : G.IsFiniteType := hG
  let D := SheafOfModules.GeneratingSections.equivOfIso (pullbackTwistIso f K L n).symm G
  have hc := @PiExponent.GeneratorsSectionCover.generators_sectionOpen_cover Y
    ((K.tensor (L.pow n)).pullback f) D ⟨hG.finite⟩
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp
    (show y ∈ ⨆ i, sectionOpen Y
      (PiExponent.GeneratorsSectionCover.generatorSection _ D i) by rw [hc]; trivial)
  exact ⟨_,hi⟩

theorem section_cover_of_jointly_surjective
    (f : Y ⟶ X) (g : Z ⟶ X) (M : LineBundle X)
    (hcover : Set.range f ∪ Set.range g = Set.univ)
    (hf : Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection f s))
    (hg : Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection g s))
    (hY : ∀ y : Y, ∃ s : GlobalSections Y (M.pullback f).sheaf, y ∈ sectionOpen Y s)
    (hZ : ∀ z : Z, ∃ s : GlobalSections Z (M.pullback g).sheaf, z ∈ sectionOpen Z s) :
    (⨆ s : GlobalSections X M.sheaf, sectionOpen X s) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ Set.range f ∪ Set.range g := by rw [hcover]; trivial
  rcases hx with ⟨y,rfl⟩ | ⟨z,rfl⟩
  · obtain ⟨s,hs⟩ := hY y
    obtain ⟨t,rfl⟩ := hf s
    apply Opens.mem_iSup.mpr
    refine ⟨t,?_⟩
    change y ∈ f ⁻¹ᵁ SectionOpens.isoOpen t
    exact (pullback_isoOpen_eq M t f).le hs
  · obtain ⟨s,hs⟩ := hZ z
    obtain ⟨t,rfl⟩ := hg s
    apply Opens.mem_iSup.mpr
    refine ⟨t,?_⟩
    change z ∈ g ⁻¹ᵁ SectionOpens.isoOpen t
    exact (pullback_isoOpen_eq M t g).le hs

theorem isAmple_of_eventual_restriction_surjective
    [NoetherianSpace Y] [NoetherianSpace Z]
    (f : Y ⟶ X) (g : Z ⟶ X) (L H : LineBundle X) (hH : H.IsAmple)
    (hcover : Set.range f ∪ Set.range g = Set.univ)
    (hY : (L.pullback f).IsAmple) (hZ : (L.pullback g).IsAmple)
    (hf : ∃ N : ℕ, ∀ n ≥ N, Function.Surjective
      (fun s : GlobalSections X (H.inverse.tensor (L.pow n)).sheaf => pullbackSection f s))
    (hg : ∃ N : ℕ, ∀ n ≥ N, Function.Surjective
      (fun s : GlobalSections X (H.inverse.tensor (L.pow n)).sheaf => pullbackSection g s)) :
    L.IsAmple := by
  obtain ⟨A,hA⟩ := eventual_pullback_twist_sections f H.inverse L hY
  obtain ⟨B,hB⟩ := eventual_pullback_twist_sections g H.inverse L hZ
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  let n := A+B+C+D+1
  have hn : 0 < n := by omega
  have hAn : A ≤ n := by omega
  have hBn : B ≤ n := by omega
  have hCn : C ≤ n := by omega
  have hDn : D ≤ n := by omega
  exact L.isAmple_of_inverse_twist_section_cover H hH hn (fun s => s)
    (section_cover_of_jointly_surjective f g (H.inverse.tensor (L.pow n)) hcover
      (hC n hCn) (hD n hDn) (hA n hAn) (hB n hBn))

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI

import OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple
import OAI.NumberTheory.PiExponent.Ampleness.LineAmpleOperations
import OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover
import OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure


variable {X : Scheme.{0}}

theorem LineBundle.IsAmple.tensor_of_section_cover {H M : LineBundle X}
    (hH : H.IsAmple) {ι : Type} (s : ι → GlobalSections X M.sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤) : (H.tensor M).IsAmple := by
  intro x V hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ i, sectionOpen X (s i) by rw [hc]; trivial)
  obtain ⟨n, hn, a, hxa, haV, haa⟩ :=
    hH x (V ⊓ sectionOpen X (s i)) ⟨hx, hi⟩
  let b : GlobalSections X (M.pow n).sheaf := powerSection (s i) n
  have hb : sectionOpen X b = sectionOpen X (s i) := M.sectionOpen_power (s i) hn
  let q : GlobalSections X ((H.tensor M).pow n).sheaf :=
    tensorSection a b ≫ (lineTensorPow H M n).inv
  have hq : sectionOpen X q = sectionOpen X a := by
    change SectionOpens.isoOpen
      (tensorSection a b ≫ (lineTensorPow H M n).symm.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    calc
      SectionOpens.isoOpen (tensorSection a b) =
          sectionOpen X a ⊓ sectionOpen X b := section_open (H.pow n) (M.pow n) a b
      _ = sectionOpen X a := by
        rw [hb, inf_eq_left.mpr (haV.trans inf_le_right)]
  exact ⟨n, hn, q, hq.symm ▸ hxa, hq.le.trans (haV.trans inf_le_left), hq.symm ▸ haa⟩

theorem LineBundle.IsAmple.tensor_of_generatingSections {H M : LineBundle X}
    (hH : H.IsAmple) (G : M.sheaf.GeneratingSections) [G.IsFiniteType] :
    (H.tensor M).IsAmple :=
  hH.tensor_of_section_cover (PiExponent.GeneratorsSectionCover.generatorSection M G)
    (PiExponent.GeneratorsSectionCover.generators_sectionOpen_cover M G)

theorem LineBundle.isAmple_of_generated_factor (L H M : LineBundle X)
    (hH : H.IsAmple) {n : ℕ} (hn : 0 < n)
    (e : (H.tensor M).sheaf ≅ (L.pow n).sheaf)
    (G : M.sheaf.GeneratingSections) [G.IsFiniteType] : L.IsAmple :=
  LineBundle.IsAmple.of_pow L hn
    (PiExponent.AmpleIso.isAmple_of_sheaf_iso (H.tensor M) (L.pow n) e
      (hH.tensor_of_generatingSections G))

def ampleInverseTwistCancel (H L : LineBundle X) (n : ℕ) :
    (H.tensor (H.inverse.tensor (L.pow n))).sheaf ≅ (L.pow n).sheaf :=
  (lineTensorAssoc H H.inverse (L.pow n)).symm ≪≫
    moduleTensorIso (lineTensorInverseIso H) (Iso.refl (L.pow n).sheaf) ≪≫
    moduleTensorUnit (L.pow n).sheaf

theorem LineBundle.isAmple_of_inverse_twist_section_cover (L H : LineBundle X)
    (hH : H.IsAmple) {n : ℕ} (hn : 0 < n) {ι : Type}
    (s : ι → GlobalSections X (H.inverse.tensor (L.pow n)).sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤) : L.IsAmple :=
  LineBundle.IsAmple.of_pow L hn
    (PiExponent.AmpleIso.isAmple_of_sheaf_iso
      (H.tensor (H.inverse.tensor (L.pow n))) (L.pow n)
      (ampleInverseTwistCancel H L n) (hH.tensor_of_section_cover s hc))

theorem LineBundle.isAmple_of_inverse_twist_generatingSections (L H : LineBundle X)
    (hH : H.IsAmple) {n : ℕ} (hn : 0 < n)
    (G : (H.inverse.tensor (L.pow n)).sheaf.GeneratingSections) [G.IsFiniteType] :
    L.IsAmple :=
  L.isAmple_of_generated_factor H (H.inverse.tensor (L.pow n)) hH hn
    (ampleInverseTwistCancel H L n) G

theorem LineBundle.isAmple_of_inverse_moduleTwist_generatingSections (L H : LineBundle X)
    (hH : H.IsAmple) {n : ℕ} (hn : 0 < n)
    (G : ((moduleTwistFunctor L n).obj H.inverse.sheaf).GeneratingSections)
    [G.IsFiniteType] : L.IsAmple := by
  let e := moduleTwistPowerIso L H.inverse.sheaf n
  let G' := SheafOfModules.GeneratingSections.equivOfIso e G
  exact @LineBundle.isAmple_of_inverse_twist_generatingSections X L H hH n hn G'
    ⟨(inferInstance : G.IsFiniteType).finite⟩

end PiExponentSeshadri.Geometry

end

end OAI

import OAI.NumberTheory.PiExponent.Ampleness.AmpleIso
import OAI.NumberTheory.PiExponent.Approximation.FramedPullback
import OAI.NumberTheory.PiExponent.Approximation.LinePullbackPowers

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X Y : Scheme.{0}}

theorem pullback_isoOpen_eq (L : LineBundle X) (s : O X ⟶ L.sheaf) (f : Y ⟶ X) :
    isoOpen (pullbackSection f s) = f ⁻¹ᵁ isoOpen s := by
  ext y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame f U e s
  calc
    y ∈ isoOpen (pullbackSection f s) ↔
        (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ (f ⁻¹ᵁ U).toScheme.basicOpen
          (coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s))) :=
      (congrArg (fun V => (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ V)
        (preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι eF)).to_iff
    _ ↔ (⟨f y,hy⟩ : U.toScheme) ∈ U.toScheme.basicOpen
          (coefficient e (restrictSection U.ι s)) := by
      rw [he,← Scheme.preimage_basicOpen_top]
      change (f ∣_ U) ⟨y,hy⟩ ∈ U.toScheme.basicOpen
        (coefficient e (restrictSection U.ι s)) ↔ _
      rw [morphismRestrict_base]
      rfl
    _ ↔ f y ∈ isoOpen s :=
      (congrArg (fun V => (⟨f y,hy⟩ : U.toScheme) ∈ V)
        (preimage_isoOpen s U.ι e)).to_iff.symm

def pullbackPowerSection (L : LineBundle X) (f : Y ⟶ X) (n : ℕ)
    (s : GlobalSections X (modulePow X L.sheaf n)) :
    GlobalSections Y (modulePow Y (L.pullback f).sheaf n) :=
  pullbackSection f s ≫ (PiExponentSeshadri.PullbackTensor.powIso f L n).hom

theorem sectionOpen_pullbackPowerSection (L : LineBundle X) (f : Y ⟶ X) (n : ℕ)
    (s : GlobalSections X (modulePow X L.sheaf n)) :
    sectionOpen Y (pullbackPowerSection L f n s) = f ⁻¹ᵁ sectionOpen X s := by
  unfold pullbackPowerSection
  erw [PiExponent.AmpleIso.sectionOpen_postcomp_iso]
  exact pullback_isoOpen_eq (L.pow n) s f

theorem LineBundle.IsAmple.pullback_closedImmersion (L : LineBundle X) (hL : L.IsAmple)
    (f : Y ⟶ X) [IsClosedImmersion f] : (L.pullback f).IsAmple := by
  intro y V hy
  obtain ⟨W,hW,hWV⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  let U : X.Opens := ⟨W,hW⟩
  have hfV : f ⁻¹ᵁ U = V := TopologicalSpace.Opens.ext hWV
  have hfy : f y ∈ U := by
    change y ∈ f ⁻¹ᵁ U
    rwa [hfV]
  obtain ⟨n,hn,s,hys,hsU,hsa⟩ := hL (f y) U hfy
  refine ⟨n,hn,pullbackPowerSection L f n s,?_,?_,?_⟩
  · rw [sectionOpen_pullbackPowerSection]
    exact hys
  · rw [sectionOpen_pullbackPowerSection, ← hfV]
    exact (Opens.map f.base).monotone hsU
  · rw [sectionOpen_pullbackPowerSection]
    exact hsa.preimage f

end
end PiExponentSeshadri.Geometry

end OAI

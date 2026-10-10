import OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover
import OAI.NumberTheory.PiExponent.Ampleness.AmpleIso
import OAI.NumberTheory.PiExponent.Ampleness.BlowupAffineSections
import OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral
import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Ampleness.RelativeAffineSectionAmple
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens PiExponentSeshadri.Projective
variable {X : Scheme.{0}}

variable {B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.eventual_ample_exceptional_twist [IsIntegral B] [CompactSpace B]
    [CompactSpace X] (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
      ((((L.pow a).pullback π).pow (n+1)).tensor J).IsAmple := by
  classical
  obtain ⟨a,ha,l,s,hs,hsa,-⟩ := L.ample_common_degree_cover hL
  let P := (L.pow a).pullback π
  let t (i : Fin l) : O B ⟶ P.sheaf := pullbackSection π (s i)
  have ht i : isoOpen (t i) = π ⁻¹ᵁ isoOpen (s i) := pullback_isoOpen_eq (L.pow a) (s i) π
  have hc : (⨆ i,isoOpen (t i)) = ⊤ := pullback_sections_cover s hs π
  have hloc (i : Fin l) : ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a)) := by
    rw [ht]
    let U : X.affineOpens := ⟨isoOpen (s i),hsa i⟩
    let : IsAffine U.1.toScheme := U.2
    exact (hπ.morphismRestrict U.1).affine_section_cover (J.restrict (π ⁻¹ᵁ U.1).ι)
      (InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι)
      (presents_morphismRestrict J ι hJ U)
  obtain ⟨N,hN⟩ := P.eventual_twist_affine_cover J t hc hloc
  refine ⟨a,N,ha,fun n hn => ?_⟩
  obtain ⟨σ,hσ,q,hq,hqa,-⟩ := hN n hn
  exact ((P.pow (n+1)).tensor J).ample_of_affine_section_cover q hq hqa

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.exists_ample_exceptional_power_gt_one
    [IsIntegral B] [CompactSpace B] [CompactSpace X]
    (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ a : ℕ, 1 < a ∧ (((L.pullback π).pow a).tensor J).IsAmple := by
  obtain ⟨a,N,ha,h⟩ := hπ.eventual_ample_exceptional_twist L hL J ι hJ
  refine ⟨a*(N+2), ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_right (N+2) (Nat.succ_le_of_lt ha)
    omega
  · apply PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ _ (h (N+1) (by omega))
    exact moduleTensorIso
      ((modulePowFunctor (N+2)).mapIso (PullbackTensor.powIso π L a) ≪≫
        linePowerMul (L.pullback π) a (N+2)) (Iso.refl _)

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

theorem exists_ample_exceptional_power_gt_one (I : X.IdealSheafData)
    (hI : I.support ≠ ⊤) (L : LineBundle X) (hL : L.IsAmple) :
    ∃ a : ℕ, 1 < a ∧
      (((L.pullback (projection I)).pow a).tensor (exceptionalLineBundle I)).IsAmple := by
  let := scheme_isIntegral I hI
  let : CompactSpace (scheme I) := QuasiCompact.compactSpace_of_compactSpace (projection I)
  exact (isBlowup I).exists_ample_exceptional_power_gt_one L hL
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I)

end PiExponentSeshadri.BlowupGluing

end

end OAI

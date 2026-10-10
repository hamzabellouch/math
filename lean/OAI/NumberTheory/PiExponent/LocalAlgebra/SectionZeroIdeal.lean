import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens
import OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections
import OAI.NumberTheory.PiExponent.Approximation.InverseDualRestriction
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent
import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionImageIdeal

namespace OAI

namespace PiExponent.SectionZeroIdeal
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionImageIdeal PiExponent.InverseFrames
variable {X : Scheme.{0}}

def zeroIdeal (L : LineBundle X) (s : GlobalSections X L.sheaf) : X.IdealSheafData := by
  letI := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  letI : L.inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  exact imageIdealSheaf (L.dualSection s)

theorem zeroIdeal_on_frame (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    (zeroIdeal L s).ideal U =
      Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  let : L.inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  change (imageIdealSheaf (L.dualSection s)).ideal U = _
  rw [imageIdealSheaf_on_frame (L.dualSection s) U
    (inverseOpenFrame (lineTensorInverseIso L) U.1 e), dualSection_restrict_coefficient]

theorem zeroIdeal_ne_bot [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : zeroIdeal L s ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨V,hxV,⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨U,hU,hxU,hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let e := restrictOpenFrame hUV eV
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  intro h
  have hi := zeroIdeal_on_frame L s ⟨U,hU⟩ e
  rw [h] at hi
  have hz : U.topIso.hom (coefficient e (restrictSection U.ι s)) = 0 := by
    have hm := Ideal.subset_span (Set.mem_singleton
      (U.topIso.hom (coefficient e (restrictSection U.ι s))))
    rw [← hi] at hm
    exact hm
  have hc : coefficient e (restrictSection U.ι s) = 0 := by
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective).mp hz
  apply hs
  apply L.restricted_coefficient_injective U.ι e
  exact hc.trans ((congrArg (coefficient e) (restrictSection_zero U.ι)).trans
    (coefficient_zero e)).symm

theorem zeroIdeal_not_surjective [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    ¬ Function.Surjective (zeroIdeal L s).subschemeι := by
  intro h
  apply zeroIdeal_ne_bot L s hs
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  apply TopologicalSpace.Closeds.ext
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact Set.range_eq_univ.mpr h

end
end PiExponent.SectionZeroIdeal

end OAI

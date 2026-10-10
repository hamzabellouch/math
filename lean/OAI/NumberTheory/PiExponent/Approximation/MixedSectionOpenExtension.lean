import OAI.NumberTheory.PiExponent.Approximation.MixedFrameExtension
import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections

namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

theorem LineBundle.mixed_section_open_extension [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (s : O X ⟶ L.sheaf)
    (hne : (sectionOpen X s : Set X).Nonempty)
    (w : O (sectionOpen X s).toScheme ⟶ M.sheaf.restrict (sectionOpen X s).ι) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t = (sectionOpen X s).ι ''ᵁ isoOpen w := by
  let U := sectionOpen X s
  obtain ⟨N,hN⟩ := L.divisible_mixed_extension M s hne (openSectionEquiv M.sheaf U w)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht,hv⟩ := hN n hn
  have hi : IsIso (restrictSection U.ι (powerSection s (n+1))) :=
    isIso_restricted_section _ _ (L.sectionOpen_power s (by omega))
  have hpre : U.ι ⁻¹ᵁ isoOpen t = isoOpen w := by
    rw [← isoOpen_restrictSection]
    have hval := mixed_value_restrict U (powerSection s (n+1)) w t hv
    have hpost := isoOpen_postcomp (tensorSection (restrictSection U.ι (powerSection s (n+1))) w)
      (moduleTensorRestrict U (L.pow (n+1)).sheaf M.sheaf).symm
    have hopen := section_open ((L.pow (n+1)).restrict U.ι) (M.restrict U.ι)
      (restrictSection U.ι (powerSection s (n+1))) w
    refine (congrArg isoOpen hval).trans (hpost.trans (hopen.trans ?_))
    have he : isoOpen (restrictSection U.ι (powerSection s (n+1))) = ⊤ := by
      apply top_unique
      intro x _
      apply (mem_isoOpen_iff _ x).mpr
      exact ⟨⊤, trivial, by infer_instance⟩
    exact (congrArg (fun V : U.toScheme.Opens => V ⊓ isoOpen w) he).trans (top_inf_eq _)
  refine ⟨t,?_⟩
  change isoOpen t = _
  rw [← hpre,Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
  exact (inf_eq_right.mpr ht).symm
end
end PiExponentSeshadri.Geometry

end OAI

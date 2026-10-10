import OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover
import OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice
import OAI.NumberTheory.PiExponent.Cohomology.EulerRegularTwists

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem exists_mono_section_of_generators [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (G : L.sheaf.GeneratingSections) [G.IsFiniteType] :
    ∃ s : GlobalSections X L.sheaf, Mono s := by
  obtain ⟨k, s, hs⟩ := PiExponent.GeneratorsSectionCover.exists_fin_section_cover L G
  exact exists_mono_section_of_finite_cover p L s hs

theorem exists_regular_twist_pair [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (H L : LineBundle X) (hH : H.IsAmple) :
    ∃ B : LineBundle X, ∃ s : GlobalSections X (L.tensor B).sheaf,
      ∃ t : GlobalSections X B.sheaf, Mono s ∧ Mono t := by
  obtain ⟨n, G, hG, G', hG'⟩ := exists_common_tensor_generators H L hH
  let : G.IsFiniteType := hG
  let : G'.IsFiniteType := hG'
  obtain ⟨s, hs⟩ := exists_mono_section_of_generators p (L.tensor (H.pow n)) G'
  obtain ⟨t, ht⟩ := exists_mono_section_of_generators p (H.pow n) G
  exact ⟨H.pow n, s, t, hs, ht⟩

end
end PiExponent.NumericalAmpleness

end OAI

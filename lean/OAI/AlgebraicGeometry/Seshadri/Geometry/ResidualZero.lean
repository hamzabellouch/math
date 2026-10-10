import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.SectionOpens
import OAI.AlgebraicGeometry.Seshadri.Geometry.ProperGlobalField

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}} [IsIntegral X]

theorem proper_nonzero_structure_section_constant
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (s : O X ⟶ O X) (hs : s ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ s = scalarEnd (baseScalars p c) := by
  obtain ⟨c,hc⟩ := proper_baseScalars_surjective p (endValue s)
  have he : s = scalarEnd (baseScalars p c) := by
    apply endValue_injective
    rw [endValue_scalarEnd,hc]
  refine ⟨c,?_,he⟩
  intro hz
  apply hs
  apply endValue_injective
  rw [← hc,hz,map_zero]
  rfl

theorem proper_nonzero_structure_section_isIso
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (s : O X ⟶ O X) (hs : s ≠ 0) : IsIso s := by
  obtain ⟨c,hc,rfl⟩ := proper_nonzero_structure_section_constant p s hs
  apply (end_isIso_iff _).mpr
  rw [endValue_scalarEnd]
  exact (isUnit_iff_ne_zero.mpr hc).map (baseScalars p)

theorem Surface.zero_power_section_everywhere (S : Surface) (L : LineBundle S.scheme)
    (s : GlobalSections S.scheme (modulePow S.scheme L.sheaf 0)) (hs : s ≠ 0) :
    isoOpen s = ⊤ := by
  let : IsIso s := proper_nonzero_structure_section_isIso S.structureMap s hs
  apply top_unique
  intro x hx
  exact (mem_isoOpen_iff s x).mpr ⟨⊤,trivial,inferInstance⟩

end
end MaximalSeshadri.Geometry

end


end OAI

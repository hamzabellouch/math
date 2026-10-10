import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierModule

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma structureMap_epi (f : X ⟶ Y) [IsClosedImmersion f] : Epi (structureMap f) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map (structureMap f)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    obtain ⟨_,⟨V,hA,rfl⟩,hyV,hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    obtain ⟨s,hs⟩ := f.app_surjective V hA
      (((F.obj ((Scheme.Modules.pushforward f).obj (unit X))).obj.map
        (homOfLE hVU).op) t)
    exact ⟨V,hVU,⟨s,hs⟩,hyV⟩
  let : Epi (F.map (structureMap f)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact F.epi_of_epi_map inferInstance

theorem closedSequence_exact (f : X ⟶ Y) [IsClosedImmersion f] :
    (ShortComplex.mk (inclusion f) (structureMap f) (kernel.condition _)).ShortExact := by
  let := structureMap_epi f
  exact { exact := ShortComplex.exact_kernel _ }

end
end MaximalSeshadri.IdealModule
end


end
end

end OAI

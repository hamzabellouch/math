import OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor

namespace OAI

namespace PiExponent.AmpleIso

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

variable {X : Scheme}

theorem sectionOpen_postcomp_iso {M N : X.Modules}
    (s : GlobalSections X M) (e : M ≅ N) :
    sectionOpen X (s ≫ e.hom) = sectionOpen X s := by
  simp only [sectionOpen, Functor.map_comp, isIso_comp_right_iff]

theorem isAmple_of_sheaf_iso (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf)
    (hL : L.IsAmple) : M.IsAmple := by
  intro x V hx
  obtain ⟨n, hn, s, hsx, hsV, hsa⟩ := hL x V hx
  let ePow : modulePow X L.sheaf n ≅ modulePow X M.sheaf n :=
    (modulePowFunctor n).mapIso e
  refine ⟨n, hn, s ≫ ePow.hom, ?_, ?_, ?_⟩
  · rwa [sectionOpen_postcomp_iso]
  · rwa [sectionOpen_postcomp_iso]
  · rwa [sectionOpen_postcomp_iso]

theorem isAmple_iff_sheaf_iso (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf) :
    L.IsAmple ↔ M.IsAmple :=
  ⟨isAmple_of_sheaf_iso L M e, isAmple_of_sheaf_iso M L e.symm⟩

end
end PiExponent.AmpleIso

end OAI

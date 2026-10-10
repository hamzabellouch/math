import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SurfaceAffineCover

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

lemma Surface.isSeparated (S : Surface) : S.scheme.IsSeparated := by
  constructor
  have : IsSeparated (S.structureMap ≫ terminal.from (Spec (CommRingCat.of ℂ))) := inferInstance
  simpa using this

theorem Surface.cohomology_zero_above_two (S : Surface) (A : LineBundle S.scheme)
    (hA : A.IsAmple) (M : S.scheme.Modules) [M.IsQuasicoherent]
    (n : ℕ) (x : cohomology M (n+3)) : x = 0 := by
  let := S.isSeparated
  obtain ⟨U,hU,hcover⟩ := S.three_affine_opens A hA
  have he : n+3 = 2+n+1 := by omega
  revert x
  rw [he]
  exact FiniteCoverCohomology.cover_ext_zero 2 U hU hcover M n

theorem Surface.lineBundle_cohomology_zero_above_two (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle S.scheme)
    (n : ℕ) (x : cohomology L.sheaf (n+3)) : x = 0 := by
  let := L.quasicoherent
  exact S.cohomology_zero_above_two A hA L.sheaf n x

end
end MaximalSeshadri.Geometry

end


end OAI

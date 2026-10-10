import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneVertex
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricH0

namespace OAI


                                       
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

theorem finite_plane_H0 (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    Module.Finite K ↥((planeVertex k s L 0 ⊓ planeVertex k s L 1) ⊓ planeVertex k s L 2) := by
  classical
  let W := planeTriple s
  let := laurentModule (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
  let := laurentTower (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
  choose d g hgen using fun i => planeVertex_finite_generators k s hs L i
  exact toric_H0_finite (planeVertex k s L) (planeVertex_stable k s L) g
    (fun i => (hgen i).1) (fun i => (hgen i).2)
    (planeVertex_cross_clearing k s (fun i => (finite_sectionsMorphism_chart k s hs i).1) L)

end
end MaximalSeshadri.Projective

end


end OAI

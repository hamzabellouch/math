import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneH0Finite
import OAI.AlgebraicGeometry.Seshadri.Geometry.SurfaceDenseProjection

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma global_plane_vertex (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M))
    (L : LineBundle X) (m : Sections k L.sheaf ⊤) (i : Fin 3) :
    (chartTop k L.sheaf (planeTriple s)).symm
      (res k L.sheaf (show planeTriple s ≤ ⊤ from le_top) m) ∈ planeVertex k s L i := by
  refine ⟨(chartTop k L.sheaf (SectionOpens.isoOpen (s i))).symm
    (res k L.sheaf (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top) m),?_⟩
  apply (chartTop k L.sheaf (planeTriple s)).injective
  rw [chartTop_nested,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,res_comp]

def globalPlaneIntersection (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    Sections k L.sheaf ⊤ →ₗ[K]
      ↥((planeVertex k s L 0 ⊓ planeVertex k s L 1) ⊓ planeVertex k s L 2) :=
  (((chartTop k L.sheaf (planeTriple s)).symm.toLinearMap).comp
    (res k L.sheaf (show planeTriple s ≤ ⊤ from le_top))).codRestrict _
      (fun m => ⟨⟨global_plane_vertex k s L m 0,global_plane_vertex k s L m 1⟩,
        global_plane_vertex k s L m 2⟩)

lemma globalPlaneIntersection_injective [IsIntegral X]
    (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X)
    [Nonempty (planeTriple s)] : Function.Injective (globalPlaneIntersection k s L) := by
  intro x y he
  apply L.restriction_injective (homOfLE (show planeTriple s ≤ ⊤ from le_top))
  exact (chartTop k L.sheaf (planeTriple s)).symm.injective (congrArg Subtype.val he)

theorem finite_projection_H0_finite [IsIntegral X]
    (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] [Nonempty (planeTriple s)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0) k
    Module.Finite K (cohomology L.sheaf 0) := by
  let := Module.compHom (cohomology L.sheaf 0) k
  let : Module.Finite K
      ↥((planeVertex k s L 0 ⊓ planeVertex k s L 1) ⊓ planeVertex k s L 2) :=
    finite_plane_H0 k s hs L
  let : Module.Finite K (Sections k L.sheaf ⊤) :=
    Module.Finite.of_injective (globalPlaneIntersection k s L) (globalPlaneIntersection_injective k s L)
  exact Module.Finite.equiv (cohomologyZero k L.sheaf).symm

theorem Surface.H0_finite (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) :
    letI := Module.compHom (cohomology L.sheaf 0) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf 0) := by
  obtain ⟨n,hn,σ,hσ,t,ht,hclosed⟩ := S.ample_embedding A hA
  let x : S.scheme := Classical.choice inferInstance
  obtain ⟨s,hs,hf,hx⟩ := @surface_finite_projection_through ℂ σ _ _ hσ S.scheme _ _
    S.structureMap _ _ (A.pow n) t ht hclosed x
  let : IsFinite (sectionsMorphism (baseScalars S.structureMap) s hs) := hf
  let : Nonempty (planeTriple s) := ⟨⟨x,⟨⟨hx 1,hx 0⟩,⟨hx 2,hx 0⟩⟩⟩⟩
  exact finite_projection_H0_finite (baseScalars S.structureMap) s hs L
end
end MaximalSeshadri.Geometry

end

end OAI

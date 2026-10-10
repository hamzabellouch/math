import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SurfaceProjection
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlanePairs

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem finite_projection_H2_finite [X.IsSeparated] [IsNoetherian X]
    (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 2) k
    Module.Finite K (cohomology L.sheaf 2) := by
  let := Module.compHom (cohomology L.sheaf 2) k
  let U := SectionOpens.isoOpen (s 1)
  let V := SectionOpens.isoOpen (s 2)
  let W := SectionOpens.isoOpen (s 0)
  have hU : IsAffineOpen U := (finite_sectionsMorphism_chart k s hs 1).1
  have hV : IsAffineOpen V := (finite_sectionsMorphism_chart k s hs 2).1
  have hW : IsAffineOpen W := (finite_sectionsMorphism_chart k s hs 0).1
  have hc : (U ⊔ V) ⊔ W = ⊤ := by
    apply top_unique
    intro x hx
    have hx' : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx'
    fin_cases i
    · exact Or.inr hi
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
  let : Module.Finite K (Sections k L.sheaf (planeTriple s) ⧸
      tripleBaseImage k L.sheaf U V W) := finite_plane_cokernel k s hs L
  exact Module.Finite.of_surjective (tripleBaseCohomologyTwo k L.sheaf U V W hc)
    (tripleBaseCohomologyTwo_surjective k L.sheaf U V W hU hV hW
      (hU.inf hV) (hU.inf hW) (hV.inf hW) hc)

theorem Surface.H2_finite (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) :
    letI := Module.compHom (cohomology L.sheaf 2) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf 2) := by
  let : S.scheme.IsSeparated := by
    constructor
    have separatedComposite : IsSeparated
        (S.structureMap ≫ Limits.terminal.from (Spec (CommRingCat.of ℂ))) := inferInstance
    simpa using separatedComposite
  obtain ⟨n,hn,s,hs,hf⟩ := S.exists_finite_projection A hA
  let : IsFinite (sectionsMorphism (baseScalars S.structureMap) s hs) := hf
  exact finite_projection_H2_finite (baseScalars S.structureMap) s hs L

end
end MaximalSeshadri.Geometry

end

end OAI

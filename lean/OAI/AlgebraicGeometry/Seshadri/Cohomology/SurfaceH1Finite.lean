import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SurfaceDenseProjection
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlaneH1Finite
import OAI.AlgebraicGeometry.Seshadri.Geometry.PlaneBoundaries
import OAI.AlgebraicGeometry.Seshadri.Cohomology.TripleTopExt

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections ModuleFlasque ModuleMayerVietoris
open MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
local instance : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) := sheafLinear X
local instance : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt
attribute [local instance] baseHomModule

lemma finite_plane_relation_quotient [IsIntegral X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] [Nonempty (planeTriple s)] (L : LineBundle X) :
    Module.Finite K (BaseHom k (planeRelations s) L.sheaf ⧸ relationBoundaries k s L) := by
  let Q := vertexBoundaries (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)
    (planeVertex k s L)
  let : Module.Finite K
      (cycles (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2) ⧸ Q) :=
    finite_plane_H1 k s hs L
  apply finite_quotient_of_kernel_le (Q.mkQ.comp (relationCycles k s L))
  intro x hx
  have hx' : relationCycles k s L x ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp hx
  obtain ⟨y,hy,he⟩ := plane_boundaries_lift k s L hx'
  have hxy : y = x := relationCycles_injective k s L he
  rwa [hxy] at hy

def planeBaseCohomologyOneMap [IsNoetherian X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i))) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) k
    (BaseHom k (planeRelations s) L.sheaf ⧸ relationBoundaries k s L) →ₗ[K]
      cohomology L.sheaf 1 := by
  letI : Algebra K Γ(X,⊤) := k.toAlgebra
  letI := Module.compHom (cohomology L.sheaf 1) k
  letI : IsScalarTower K Γ(X,⊤) (cohomology L.sheaf 1) := .of_algebraMap_smul (fun _ _ => rfl)
  letI : Module K (planeRelations s ⟶ L.sheaf) := Module.compHom (planeRelations s ⟶ L.sheaf) k
  letI : IsScalarTower K Γ(X,⊤) (planeRelations s ⟶ L.sheaf) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have hc : (SectionOpens.isoOpen (s 0) ⊔ SectionOpens.isoOpen (s 1)) ⊔
      SectionOpens.isoOpen (s 2) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hs ▸ hx)
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  let F := (tripleTopHomCohomologyOne L.sheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2)) (h 0) (h 1) (h 2) hc).restrictScalars K
  refine (relationBoundaries k s L).liftQ F ?_
  intro x hx
  exact tripleTopHomCohomologyOne_zero L.sheaf _ _ _ (h 0) (h 1) (h 2) hc x hx

lemma planeBaseCohomologyOneMap_surjective [IsNoetherian X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i))) (L : LineBundle X) :
    Function.Surjective (planeBaseCohomologyOneMap k s hs h L) := by
  intro y
  have hc : (SectionOpens.isoOpen (s 0) ⊔ SectionOpens.isoOpen (s 1)) ⊔
      SectionOpens.isoOpen (s 2) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hs ▸ hx)
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  obtain ⟨x,hx⟩ := tripleTopHomCohomologyOne_surjective L.sheaf
    (SectionOpens.isoOpen (s 0)) (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
      (h 0) (h 1) (h 2) hc y
  exact ⟨(relationBoundaries k s L).mkQ x,hx⟩

theorem finite_projection_H1_finite [IsIntegral X] [IsNoetherian X]
    (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] [Nonempty (planeTriple s)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) k
    Module.Finite K (cohomology L.sheaf 1) := by
  let := Module.compHom (cohomology L.sheaf 1) k
  let : Module.Finite K
      (BaseHom k (planeRelations s) L.sheaf ⧸ relationBoundaries k s L) :=
    finite_plane_relation_quotient k s hs L
  exact Module.Finite.of_surjective (planeBaseCohomologyOneMap k s hs
    (fun i => (finite_sectionsMorphism_chart k s hs i).1) L)
    (planeBaseCohomologyOneMap_surjective k s hs
      (fun i => (finite_sectionsMorphism_chart k s hs i).1) L)

theorem Surface.H1_finite (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) :
    letI := Module.compHom (cohomology L.sheaf 1) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf 1) := by
  obtain ⟨n,hn,σ,hσ,t,ht,hclosed⟩ := S.ample_embedding A hA
  let x : S.scheme := Classical.choice inferInstance
  obtain ⟨s,hs,hf,hx⟩ := @surface_finite_projection_through ℂ σ _ _ hσ S.scheme _ _
    S.structureMap _ _ (A.pow n) t ht hclosed x
  let : IsFinite (sectionsMorphism (baseScalars S.structureMap) s hs) := hf
  let : Nonempty (planeTriple s) := ⟨⟨x,⟨⟨hx 1,hx 0⟩,⟨hx 2,hx 0⟩⟩⟩⟩
  exact finite_projection_H1_finite (baseScalars S.structureMap) s hs L

end
end MaximalSeshadri.Geometry

end

end OAI

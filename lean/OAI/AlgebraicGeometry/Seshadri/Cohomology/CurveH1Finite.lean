import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurveProjection
import OAI.AlgebraicGeometry.Seshadri.Cohomology.BaseCech

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} [IsNoetherian X]

theorem finite_pencil_H1_finite (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) k
    Module.Finite K (cohomology L.sheaf 1) := by
  let U := SectionOpens.isoOpen (s false)
  let V := SectionOpens.isoOpen (s true)
  obtain ⟨hU,_⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,_⟩ := finite_pencil_chart k s hs true
  have hc : U ⊔ V = ⊤ := by
    apply top_unique
    intro x hx
    have : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp this
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  let := Module.compHom (cohomology L.sheaf 1) k
  let := finite_pencil_cokernel k s hs L
  let e := twoBaseCohomologyOne k L.sheaf U V hU hV hc
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

theorem projective_curve_H1_finite {σ : Type} [Fintype σ] [Infinite K]
    [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1)
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    Module.Finite K (cohomology L.sheaf 1) := by
  obtain ⟨t,ht,hf⟩ := projective_curve_finite_pencil p hd s hs
  let := hf
  exact finite_pencil_H1_finite _ t ht L
end
end MaximalSeshadri.Geometry
end


end
end

end OAI

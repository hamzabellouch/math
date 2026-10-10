import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ToricH1
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlanePairToric

namespace OAI


                                       
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

theorem finite_plane_H1 (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    Module.Finite K ((cycles (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)) ⧸
      vertexBoundaries (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)
        (planeVertex k s L)) := by
  classical
  let W := planeTriple s
  let := laurentModule (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
  let := laurentTower (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
  have haff i := (finite_sectionsMorphism_chart k s hs i).1
  choose d g hgen using fun i => planeVertex_finite_generators k s hs L i
  have genA : planePair k s L 0 1 = monomialSpan (K := K) coneA (g 0) := by
    apply localized_span (vertexCone 0) coneA (g 0) _
      (fun a => planeVertex_le_pair k s L 0 1 ((hgen 0).1 a)) (planePair_stable01 k s L)
    intro x hx
    obtain ⟨n,hn⟩ := planePair_clearing k s haff L 0 1 x hx
    refine ⟨n • (weight 1-weight 0),?_,?_⟩
    · rw [← (hgen 0).2]; exact hn
    · intro w hw
      have hw' : 0 ≤ w.2 := hw.1
      change 0 ≤ (-(n • (weight 1-weight 0))+w).2
      simpa [weight] using hw'
  have genB : planePair k s L 0 2 = monomialSpan (K := K) coneB (g 0) := by
    apply localized_span (vertexCone 0) coneB (g 0) _
      (fun a => planeVertex_le_pair k s L 0 2 ((hgen 0).1 a)) (planePair_stable02 k s L)
    intro x hx
    obtain ⟨n,hn⟩ := planePair_clearing k s haff L 0 2 x hx
    refine ⟨n • (weight 2-weight 0),?_,?_⟩
    · rw [← (hgen 0).2]; exact hn
    · intro w hw
      have hw' : 0 ≤ w.1 := hw.2
      change 0 ≤ (-(n • (weight 2-weight 0))+w).1
      simpa [weight] using hw'
  have genC : planePair k s L 1 2 = monomialSpan (K := K) (coneC 0) (g 1) := by
    apply localized_span (vertexCone 1) (coneC 0) (g 1) _
      (fun a => planeVertex_le_pair k s L 1 2 ((hgen 1).1 a)) (planePair_stable12 k s L)
    intro x hx
    obtain ⟨n,hn⟩ := planePair_clearing k s haff L 1 2 x hx
    refine ⟨n • (weight 2-weight 1),?_,?_⟩
    · rw [← (hgen 1).2]; exact hn
    · intro w hw
      have hw' : w.1+w.2 ≤ 0 := hw.2
      change (-(n • (weight 2-weight 1))+w).1 + (-(n • (weight 2-weight 1))+w).2 ≤ 0
      simp only [Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg,Prod.smul_fst,Prod.smul_snd]
      simp [weight] at ⊢
      omega
  exact toric_H1_finite (planeVertex k s L) (planeVertex_stable k s L) g (fun i a => (hgen i).1 a)
    (planeVertex_cross_clearing k s haff L) _ _ _ (planePair_stable01 k s L)
    (planePair_stable02 k s L) (planePair_stable12 k s L)
    (planeVertex_le_pair k s L 0 1) (planeVertex_le_pair k s L 0 2) (planeVertex_le_pair k s L 1 2)
    genA genB genC

end
end MaximalSeshadri.Projective

end


end OAI

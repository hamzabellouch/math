import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CurveCohomology
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CurveH0Finite
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CurveH1Finite

namespace OAI

section
noncomputable section
                                                   
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

theorem projective_curve_cohomology_finite
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (L : LineBundle X) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n)
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    Module.Finite K (cohomology L.sheaf n) := by
  cases n with
  | zero => exact projective_curve_H0_finite p hd s hs L
  | succ n => cases n with
    | zero => exact projective_curve_H1_finite p hd s hs L
    | succ n =>
      let := Module.compHom (cohomology L.sheaf (n+2))
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
      have : L.sheaf.IsQuasicoherent := L.quasicoherent
      have : Subsingleton (cohomology L.sheaf (n+2)) := ⟨fun x y =>
        (projective_curve_ext_zero p hd s hs L.sheaf n x).trans
          (projective_curve_ext_zero p hd s hs L.sheaf n y).symm⟩
      infer_instance
end
end MaximalSeshadri.Geometry
end


end
end

end OAI

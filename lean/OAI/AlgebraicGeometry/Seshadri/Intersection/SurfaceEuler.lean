import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.ClosedPushforwardEuler
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceCohomology
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceH0Finite
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceH1Finite
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceH2Finite

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.cohomology_finite (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf n) := by
  cases n with
  | zero => exact S.H0_finite A hA L
  | succ n => cases n with
    | zero => exact S.H1_finite A hA L
    | succ n => cases n with
      | zero => exact S.H2_finite A hA L
      | succ n =>
        let := Module.compHom (cohomology L.sheaf (n+3)) (baseScalars S.structureMap)
        let : Subsingleton (cohomology L.sheaf (n+3)) := ⟨fun x y =>
          (S.lineBundle_cohomology_zero_above_two A hA L n x).trans
            (S.lineBundle_cohomology_zero_above_two A hA L n y).symm⟩
        infer_instance

theorem IntegralCurve.cohomology_zero_above_one (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme)
    (n : ℕ) (x : cohomology L.sheaf (n+2)) : x = 0 := by
  obtain ⟨σ,hσ,M,a,ha,hc⟩ := C.exists_projective_sections S A hA
  let := hσ
  let := L.quasicoherent
  let : IsClosedImmersion (sectionsMorphism
    ((C.embedding ≫ S.structureMap).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) := hc
  exact projective_curve_ext_zero (C.embedding ≫ S.structureMap) C.dimension a ha L.sheaf n x

lemma IntegralCurve.euler_two_eq_one (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme) :
    eulerCharacteristic (C.embedding ≫ S.structureMap) 2 L.sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1 L.sheaf := by
  have hz : Subsingleton (cohomology L.sheaf 2) := ⟨fun x y =>
    (C.cohomology_zero_above_one S A hA L 0 x).trans
      (C.cohomology_zero_above_one S A hA L 0 y).symm⟩
  let := hz
  have hd : cohomologyDimension (C.embedding ≫ S.structureMap) L.sheaf 2 = 0 := by
    simp [cohomologyDimension,Module.finrank_zero_of_subsingleton]
  change (∑ n ∈ Finset.range (2+1), (-1 : ℤ)^n *
    (cohomologyDimension (C.embedding ≫ S.structureMap) L.sheaf n : ℤ)) = _
  rw [Finset.sum_range_succ,hd]
  simp only [Nat.cast_zero,mul_zero,add_zero]
  rfl

theorem IntegralCurve.pushforward_cohomology_finite (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n)
      (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n) := by
  let := Module.compHom (cohomology L.sheaf n) (baseScalars (C.embedding ≫ S.structureMap))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n)
    (baseScalars S.structureMap)
  let := C.cohomology_finite S A hA L n
  exact Module.Finite.equiv (ClosedPushforward.cohomologyEquiv C.embedding S.structureMap L.sheaf n)

lemma IntegralCurve.euler_pushforward (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme) :
    eulerCharacteristic S.structureMap 2 ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1 L.sheaf := by
  rw [ClosedPushforward.euler_pushforward,C.euler_two_eq_one S A hA]

end
end MaximalSeshadri.Geometry

end


end OAI

import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceFuel
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceOrbit
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceNext
import OAI.Analysis.MatrixSigning.Complexity.PolynomialIterateFamilies

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι : Type*} {L : ι → ℕ}
lemma isPoly_orbitStencil (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    IsPoly (fun s : {s : ι×ℕ // ((a s.1).orbit s.2).n≠0} => L s.val.1)
      (fun s => ((a s.val.1).orbit s.val.2).stencilCount) := by
  obtain ⟨q,hq⟩ := (isPoly_face_dimensions a ha).eval (RationalSDP.valueScanP Schedule.queryPrecisionP)
  refine ⟨q,?_⟩
  intro s
  exact (orbit_query_bounds (a s.val.1) (hg s.val.1) s.val.2 s.property).1.trans (hq s.val.1)
lemma isPoly_orbitScore (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    IsPoly (fun s : {s : ι×ℕ // ((a s.1).orbit s.2).n≠0} => L s.val.1)
      (fun s => ((a s.val.1).orbit s.val.2).scoreCount) := by
  obtain ⟨q,hq⟩ := (isPoly_face_dimensions a ha).eval (RationalSDP.valueScanP Schedule.queryPrecisionP)
  refine ⟨q,?_⟩
  intro s
  exact (orbit_query_bounds (a s.val.1) (hg s.val.1) s.val.2 s.property).2.trans (hq s.val.1)
lemma runsPoly_orbitStep (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    RunsPoly (fun s : ι×ℕ => L s.1) faceNext (fun s => (a s.1).orbit s.2) :=
  runsPoly_faceNext _ (isPoly_face_orbit a ha hg) (isPoly_orbitStencil a ha hg) (isPoly_orbitScore a ha hg)

lemma runsPoly_normalFaceRun (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    RunsPoly L faceRun (fun i => (a i).normal) := by
  have hi : IsPoly L (fun i => (faceCode (a i).normal).length) :=
    (RunsPoly.of_poly faceNormalized a ha).output
  have hfuel := ((isPoly_face_dimensions a ha).eval Schedule.iterationP).mono
    (fun i => normal_fuel_bound (a i) (hg i))
  have hf := runsPoly_fFuel (fun i => (a i).normal) hi hfuel
  have hs := RunsPoly.of_poly faceStart (fun i => (a i).normal) hi
  have hstep := runsPoly_orbitStep a ha hg
  unfold faceRun
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply (hf.both hs).then
  apply runsPoly_iterate _ _ (hf.both hs).output
  obtain ⟨p,hp⟩ := hstep.cost
  exact ⟨p,fun i j _ => hp (i,j)⟩

lemma runsPoly_normalizedRun (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    RunsPoly L normalizedRun a :=
  (RunsPoly.of_poly faceNormalized a ha).then (runsPoly_normalFaceRun a ha hg)
end CurrentKS.Realization

end

end OAI

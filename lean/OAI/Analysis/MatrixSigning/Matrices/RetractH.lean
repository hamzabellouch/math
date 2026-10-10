import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.JordanCLM

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

private local instance : NormedAddCommGroup (Mat d) := inferInstance
private local instance : NormedSpace ℝ (Mat d) := inferInstance
private local instance : TopologicalSpace (Mat d) :=
  (inferInstance : NormedAddCommGroup (Mat d)).toUniformSpace.toTopologicalSpace

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

def retractH : Mat d →L[ℝ] H d := (hermitianSubmodule d).orthogonalProjectionOnto

@[simp] lemma retractH_coe (A : H d) : retractH (A : Mat d) = A :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self A

lemma invH_retract (A : H d) : invH A = retractH (Ring.inverse (A : Mat d)) := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact (retractH_coe (invH A)).symm

lemma contDiffAt_invH {A : H d} (hA : A ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n invH A := by
  obtain ⟨a,ha⟩ := hA.isUnit
  have hi : ContDiffAt ℝ n Ring.inverse (A : Mat d) := by
    rw [← ha]
    exact contDiffAt_ringInverse ℝ a
  have hc := (retractH (d := d)).contDiff.contDiffAt.comp A
    (hi.comp A (hermitianSubmodule d).subtypeL.contDiff.contDiffAt)
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun B => invH_retract B

lemma hasFDerivAt_invH {A : H d} (hA : A ∈ pd d) :
    HasFDerivAt invH (-sandwichCLM (invH A)) A := by
  obtain ⟨a,ha⟩ := hA.isUnit
  have hi : HasFDerivAt (fun B : Mat d => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Mat d) (A : Mat d)⁻¹ (A : Mat d)⁻¹) (A : Mat d) := by
    rw [← ha]
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Matrix.coe_units_inv] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) a)
  have hc := (retractH (d := d)).hasFDerivAt.comp A
    (hi.comp A (hermitianSubmodule d).subtypeL.hasFDerivAt)
  have he : (fun B : H d => retractH ((B : Mat d)⁻¹)) = invH := by
    funext B
    exact retractH_coe (invH B)
  change HasFDerivAt (fun B : H d => retractH ((B : Mat d)⁻¹)) _ A at hc
  rw [he] at hc
  refine hc.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro U
  change -sandwich (invH A) U = retractH (-((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹))
  rw [map_neg]
  exact congrArg Neg.neg (retractH_coe (sandwich (invH A) U)).symm

lemma contDiff_sandwich {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : H d × H d => sandwich z.1 z.2) := by
  have hf : (fun z : H d × H d => sandwich z.1 z.2) =
      (fun z : H d × H d => retractH ((z.1 : Mat d) * (z.2 : Mat d) * (z.1 : Mat d))) := by
    funext z
    exact (retractH_coe (sandwich z.1 z.2)).symm
  rw [hf]
  apply (retractH (d := d)).contDiff.comp
  exact (((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_fst).mul
    ((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_snd)).mul
      ((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_fst)

lemma hasFDerivAt_invSandwich (A P : H d) (hA : A ∈ pd d) :
    HasFDerivAt (fun z : H d × H d => sandwich (invH z.1) z.2)
      ((-jordanCLM (invH A) (sandwich (invH A) P)).comp (ContinuousLinearMap.fst ℝ (H d) (H d)) +
       (sandwichCLM (invH A)).comp (ContinuousLinearMap.snd ℝ (H d) (H d))) (A,P) := by
  let val := (hermitianSubmodule d).subtypeL
  have hInv := val.hasFDerivAt.comp (A,P)
    ((hasFDerivAt_invH hA).comp (A,P) (hasFDerivAt_fst (p := (A,P))))
  have hMid := val.hasFDerivAt.comp (A,P) (hasFDerivAt_snd (p := (A,P)))
  have hm := (hInv.mul' hMid).mul' hInv
  have hh := (retractH (d := d)).hasFDerivAt.comp (A,P) hm
  have he : (fun z : H d × H d => retractH
      (((invH z.1 : H d) : Mat d) * (z.2 : Mat d) * ((invH z.1 : H d) : Mat d))) =
      (fun z : H d × H d => sandwich (invH z.1) z.2) := by
    funext z
    exact retractH_coe (sandwich (invH z.1) z.2)
  change HasFDerivAt (fun z : H d × H d => retractH
    (((invH z.1 : H d) : Mat d) * (z.2 : Mat d) * ((invH z.1 : H d) : Mat d))) _ (A,P) at hh
  rw [he] at hh
  refine hh.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro z
  change -jordanCLM (invH A) (sandwich (invH A) P) z.1 + sandwich (invH A) z.2 =
    retractH
      (((invH A : H d) : Mat d) * (P : Mat d) *
          (-(((invH A : H d) : Mat d) * (z.1 : Mat d) * ((invH A : H d) : Mat d))) +
       (((invH A : H d) : Mat d) * (z.2 : Mat d) +
          (-(((invH A : H d) : Mat d) * (z.1 : Mat d) * ((invH A : H d) : Mat d))) * (P : Mat d)) *
        ((invH A : H d) : Mat d))
  rw [← retractH_coe (-jordanCLM (invH A) (sandwich (invH A) P) z.1 + sandwich (invH A) z.2)]
  congr 1
  simp only [Submodule.coe_add, Submodule.coe_neg, jordanCLM_val, sandwich_val]
  noncomm_ring

lemma contDiffAt_invSandwich (A P : H d) (hA : A ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun z : H d × H d => sandwich (invH z.1) z.2) (A,P) := by
  have hi : ContDiffAt ℝ n (fun z : H d × H d => invH z.1) (A,P) :=
    (contDiffAt_invH (d := d) (A := A) (n := n) hA).fst' (y := P)
  have hp : ContDiffAt ℝ n (fun z : H d × H d => (invH z.1, z.2)) (A,P) :=
    hi.prodMk (contDiffAt_snd (𝕜 := ℝ) (n := n) (p := (A,P)))
  have hs : ContDiffAt ℝ n (fun u : H d × H d => sandwich u.1 u.2) (invH A,P) :=
    (contDiff_sandwich (d := d) (n := n)).contDiffAt
  exact hs.comp (A,P) hp

end CurrentKS.Hermitian

end

end OAI

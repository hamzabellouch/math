import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.InvH

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section L2Operator

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma isOpen_pd [NeZero d] : IsOpen (pd d) := by
  let : CStarAlgebra (Mat d) := {}
  have he : pd d = interior (psdCone d : Set (H d)) ∩
      {A : H d | IsUnit (A : Mat d)} := by
    ext A
    constructor
    · intro hA
      exact ⟨posDef_mem_interior A hA, hA.isUnit⟩
    · rintro ⟨hA, hu⟩
      exact (interior_subset hA).posDef_iff_isUnit.mpr hu
  rw [he]
  exact isOpen_interior.inter (Units.isOpen.preimage continuous_subtype_val)

def sandwich (A U : H d) : H d :=
  ⟨(A : Mat d) * (U : Mat d) * (A : Mat d), by
    have hh := Matrix.isHermitian_mul_mul_conjTranspose (A : Mat d) U.property
    rw [A.property.eq] at hh
    exact hh⟩

@[simp] lemma sandwich_val (A U : H d) :
    (sandwich A U : Mat d) = (A : Mat d) * (U : Mat d) * (A : Mat d) := rfl

lemma sandwich_psd (A U : H d) (hU : U ∈ psdCone d) : sandwich A U ∈ psdCone d := by
  have hh := hU.mul_mul_conjTranspose_same (A : Mat d)
  rw [A.property.eq] at hh
  exact hh

def matrixTraceCLM : Mat d →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap (Fin d) ℝ ℂ).toContinuousLinearMap

@[simp] lemma matrixTraceCLM_apply (A : Mat d) : matrixTraceCLM A = A.trace.re := rfl

lemma hasDerivAt_matrix_inverse (A U : H d) (hA : A ∈ pd d) :
    HasDerivAt (fun r : ℝ => ((A : Mat d) + r • (U : Mat d))⁻¹)
      (-((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹)) 0 := by
  obtain ⟨a, ha⟩ := hA.isUnit
  have hcurve : HasDerivAt (fun r : ℝ => (A : Mat d) + r • (U : Mat d)) (U : Mat d) 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) (A : Mat d)).add
      ((hasDerivAt_id' (0 : ℝ)).smul_const (U : Mat d))
    simp only [zero_add, one_smul] at hh
    exact hh
  have hInv := (hasFDerivAt_ringInverse (𝕜 := ℝ) a)
  rw [ha] at hInv
  have hz : (A : Mat d) = (fun r : ℝ => (A : Mat d) + r • (U : Mat d)) 0 := by
    ext i j
    simp [Matrix.add_apply]
  have hd := hInv.comp_hasDerivAt_of_eq (0 : ℝ) hcurve hz
  have hi : (↑a⁻¹ : Mat d) = (A : Mat d)⁻¹ := by rw [Matrix.coe_units_inv, ha]
  convert hd using 1 <;> try rfl
  · funext r
    exact Matrix.nonsing_inv_eq_ringInverse _
  · simp only [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hi]

end L2Operator

section Frobenius

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma inner_sandwich (A U P : H d) :
    inner ℝ P (sandwich A U) = inner ℝ (sandwich A P) U := by
  rw [inner_eq_trace, inner_eq_trace]
  change ((P : Mat d) * ((A : Mat d) * (U : Mat d) * (A : Mat d))).trace.re =
    ((A : Mat d) * (P : Mat d) * (A : Mat d) * (U : Mat d)).trace.re
  rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm ((P : Mat d) * (A : Mat d) * (U : Mat d))]
  simp only [mul_assoc]

lemma hasDerivAt_trace_inverse (A U P : H d) (hA : A ∈ pd d) :
    HasDerivAt (fun r : ℝ => inner ℝ P (invH (A + r • U)))
      (-inner ℝ (sandwich (invH A) P) U) 0 := by
  have hi := hasDerivAt_matrix_inverse A U hA
  have hm := (hasDerivAt_const (0 : ℝ) (P : Mat d)).mul hi
  have ht := (matrixTraceCLM (d := d)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hm
  have hfun : (fun r : ℝ => (matrixTraceCLM (d := d)) ((P : Mat d) *
      ((A : Mat d) + r • (U : Mat d))⁻¹)) =
      (fun r : ℝ => inner ℝ P (invH (A + r • U))) := by
    funext r
    rw [inner_eq_trace]
    rfl
  change HasDerivAt (fun r : ℝ => (matrixTraceCLM (d := d)) ((P : Mat d) *
    ((A : Mat d) + r • (U : Mat d))⁻¹)) _ (0 : ℝ) at ht
  rw [hfun] at ht
  simp only [zero_mul, zero_add, mul_neg] at ht
  convert ht using 1
  rw [← inner_sandwich, inner_eq_trace]
  change -((P : Mat d) * ((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹)).trace.re =
    (-((P : Mat d) * ((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹))).trace.re
  simp only [Matrix.trace_neg, Complex.neg_re]

end Frobenius

end CurrentKS.Hermitian

end

end OAI

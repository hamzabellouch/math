import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.TraceCLM
import OAI.Analysis.MatrixSigning.Matrices.Sandwich

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma inner_right_one (A : H d) : inner ℝ A (one : H d) = realTrace A := by
  rw [real_inner_comm, inner_one]

lemma hasDerivAt_inner_curve (B X U : H d) :
    HasDerivAt (fun r : ℝ => inner ℝ B (X + r • U)) (inner ℝ B U) 0 := by
  simp only [inner_add_right, inner_smul_rightH]
  have hh := (hasDerivAt_const (0 : ℝ) (inner ℝ B X)).add
      ((hasDerivAt_id' (0 : ℝ)).mul_const (inner ℝ B U))
  simp only [zero_add, one_mul] at hh
  exact hh

lemma inverse_trace_stationarity [NeZero d] (P B X : H d) (hX : X ∈ pd d)
    (hmin : ∀ Z ∈ pd d, inner ℝ P (invH X) + inner ℝ B X ≤
      inner ℝ P (invH Z) + inner ℝ B Z) : sandwich (invH X) P = B := by
  apply ext_inner_right ℝ
  intro U
  have hd := (hasDerivAt_trace_inverse X U P hX).add (hasDerivAt_inner_curve B X U)
  have hc : Continuous (fun r : ℝ => X + r • U) := by fun_prop
  have hn : ∀ᶠ r : ℝ in nhds 0, X + r • U ∈ pd d := by
    have h0 : X + (0 : ℝ) • U ∈ pd d := by simpa using hX
    exact (hc.continuousAt.preimage_mem_nhds (isOpen_pd.mem_nhds h0))
  have hm : IsLocalMin (fun r : ℝ => inner ℝ P (invH (X + r • U)) +
      inner ℝ B (X + r • U)) 0 := by
    filter_upwards [hn] with r hr
    simpa only [zero_smul, add_zero] using hmin (X + r • U) hr
  have he := hm.hasDerivAt_eq_zero hd
  linarith

lemma sandwich_add (A U V : H d) : sandwich A (U+V) = sandwich A U + sandwich A V := by
  apply Subtype.ext
  change (A : Mat d) * ((U : Mat d)+(V : Mat d)) * (A : Mat d) = _
  simp only [mul_add, add_mul]
  rfl

lemma sandwich_smul (r : ℝ) (A U : H d) : sandwich A (r • U) = r • sandwich A U := by
  apply Subtype.ext
  change (A : Mat d) * (r • (U : Mat d)) * (A : Mat d) = r • _
  simp only [mul_smul_comm, smul_mul_assoc]
  rfl

lemma sandwich_inverse_cancel (X P : H d) (hX : X ∈ pd d) :
    sandwich X (sandwich (invH X) P) = P := by
  apply Subtype.ext
  let : Invertible (X : Mat d) := hX.isUnit.invertible
  change (X : Mat d) * ((X : Mat d)⁻¹ * (P : Mat d) * (X : Mat d)⁻¹) * (X : Mat d) = _
  have hu := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  simp only [mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ hu]

lemma sandwich_pd (A B : H d) (hA : A ∈ pd d) (hB : B ∈ pd d) :
    sandwich A B ∈ pd d := by
  have hh := hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hA.isUnit)
  rw [A.property.eq] at hh
  exact hh

lemma pd_sum_scalar {A : H d} (hA : A ∈ psdCone d) {ε : ℝ} (hε : 0 < ε) :
    A + ε • (one : H d) ∈ pd d := by
  have hh := (scalar_posDef hε).add_posSemidef hA
  rw [add_comm] at hh
  exact hh

lemma trace_zero_psd {A : H d} (hA : A ∈ psdCone d) (htr : realTrace A = 0) : A = 0 := by
  apply le_antisymm
  · simpa only [htr, zero_smul] using trace_bound_above hA
  · exact psd_nonneg hA

end
end CurrentKS.Hermitian

end OAI

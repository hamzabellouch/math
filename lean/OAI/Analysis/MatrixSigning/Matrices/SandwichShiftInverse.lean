import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.Sandwich
import OAI.Analysis.MatrixSigning.Matrices.RankFactor

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma sandwich_shift_inverse (X U : H d) (hX : X ∈ pd d) (r : ℝ) :
    sandwich (U-r • X) (invH X) = sandwich U (invH X) - (2*r) • U + r^2 • X := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  apply Subtype.ext
  change ((U : Mat d)-r • (X : Mat d)) * (X : Mat d)⁻¹ * ((U : Mat d)-r • (X : Mat d)) =
    (U : Mat d) * (X : Mat d)⁻¹ * (U : Mat d) - (2*r) • (U : Mat d) + r^2 • (X : Mat d)
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm, mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hx, Matrix.nonsing_inv_mul _ hx, mul_one]
  module

lemma trace_inverse_cauchy (A X U : H d) (hA : A ∈ psdCone d) (hX : X ∈ pd d) :
    (inner ℝ A U)^2 ≤ inner ℝ A X * inner ℝ A (sandwich U (invH X)) := by
  have hn (r : ℝ) := inner_nonneg_of_psd A (sandwich (U-r • X) (invH X))
    hA (sandwich_psd _ _ hX.inv.posSemidef)
  have hn' (r : ℝ) : 0 ≤ inner ℝ A (sandwich U (invH X)) -
      (2*r)*inner ℝ A U + r^2*inner ℝ A X := by
    have hh := hn r
    rw [sandwich_shift_inverse X U hX,inner_add_right,inner_sub_right,
      real_inner_smul_right A U (2*r),real_inner_smul_right A X (r^2)] at hh
    exact hh
  have hh := discrim_le_zero (a := inner ℝ A X) (b := -2*inner ℝ A U)
    (c := inner ℝ A (sandwich U (invH X))) (fun r => by nlinarith [hn' r])
  rw [discrim] at hh
  nlinarith

lemma trace_mul_real (A B : H d) : (((A : Mat d)*(B : Mat d)).trace.re : ℂ) = ((A : Mat d)*(B : Mat d)).trace := by
  have hs : star (((A : Mat d)*(B : Mat d)).trace) = ((A : Mat d)*(B : Mat d)).trace := by
    rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,A.property.eq,B.property.eq,Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.mp hs

lemma sandwich_rank_one (A B : H d) (hA : A ∈ psdCone d) (hrank : (A : Mat d).rank ≤ 1) :
    sandwich A B = (inner ℝ A B) • A := by
  apply Subtype.ext
  change (A : Mat d)*(B : Mat d)*(A : Mat d) = (inner ℝ A B) • (A : Mat d)
  rw [CurrentKS.rank_one_sandwich _ hA hrank,inner_eq_trace]
  have hs (r : ℝ) : r • (A : Mat d) = (r : ℂ) • (A : Mat d) := by
    ext i j
    exact Complex.real_smul
  rw [hs,trace_mul_real]

lemma trace_inverse_young (A X U : H d) (hA : A ∈ psdCone d) (hX : X ∈ pd d)
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    2*t*inner ℝ A U ≤ s*inner ℝ A (sandwich U (invH X)) + t^2/s*inner ℝ A X := by
  have hn := inner_nonneg_of_psd A (sandwich (U-(t/s) • X) (invH X)) hA
    (sandwich_psd _ _ hX.inv.posSemidef)
  rw [sandwich_shift_inverse X U hX,inner_add_right,inner_sub_right,
    real_inner_smul_right A U (2*(t/s)),real_inner_smul_right A X ((t/s)^2)] at hn
  have hh := mul_nonneg hs.le hn
  field_simp at hh ⊢
  nlinarith

end CurrentKS.Hermitian

end

end OAI

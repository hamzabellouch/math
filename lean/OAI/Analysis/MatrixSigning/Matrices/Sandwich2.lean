import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PosLower

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma sandwich_zero (A : H d) : sandwich A 0 = 0 := by
  apply Subtype.ext
  simp [sandwich]

lemma sandwich_eq_zero_iff [NeZero d] (U B : H d) (hB : B ∈ pd d) :
    sandwich U B = 0 ↔ U = 0 := by
  constructor
  · intro he
    have hz : inner ℝ B (sandwich U Hermitian.one) = 0 := by
      rw [real_inner_comm, ← inner_sandwich, he, inner_zero_right]
    have hs := eq_zero_of_inner_pd hB (sandwich_psd U _ one_mem_psdCone) hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [inner_eq_trace]
    have hv : (U : Mat d) * (U : Mat d) = 0 := by
      have hh := congrArg Subtype.val hs
      simpa only [sandwich_val, one_val, mul_one, ZeroMemClass.coe_zero] using hh
    rw [hv]
    simp
  · rintro rfl
    apply Subtype.ext
    simp [sandwich]

lemma inverse_remainder (X Z : H d) (hX : X ∈ pd d) (hZ : Z ∈ pd d) :
    invH Z - invH X + sandwich (invH X) (Z-X) =
      sandwich (invH X) (sandwich (Z-X) (invH Z)) := by
  have hx := (Matrix.isUnit_iff_isUnit_det (X : Mat d)).mp hX.isUnit
  have hz := (Matrix.isUnit_iff_isUnit_det (Z : Mat d)).mp hZ.isUnit
  apply Subtype.ext
  change (Z : Mat d)⁻¹ - (X : Mat d)⁻¹ +
    (X : Mat d)⁻¹ * ((Z : Mat d)-(X : Mat d)) * (X : Mat d)⁻¹ =
    (X : Mat d)⁻¹ * (((Z : Mat d)-(X : Mat d)) * (Z : Mat d)⁻¹ *
      ((Z : Mat d)-(X : Mat d))) * (X : Mat d)⁻¹
  symm
  calc
    _ = ((X : Mat d)⁻¹ - (Z : Mat d)⁻¹) * ((Z : Mat d)-(X : Mat d)) * (X : Mat d)⁻¹ := by
      rw [Matrix.inv_sub_inv (show IsUnit (X : Mat d) ↔ IsUnit (Z : Mat d) from
        ⟨fun _ => hZ.isUnit, fun _ => hX.isUnit⟩)]
      simp only [mul_assoc]
    _ = _ := by
      simp only [sub_mul, mul_sub, mul_assoc,
        Matrix.mul_nonsing_inv _ hx,
        Matrix.nonsing_inv_mul_cancel_left _ _ hz, mul_one]
      abel

lemma inverse_trace_gap (P X Z : H d) (hX : X ∈ pd d) (hZ : Z ∈ pd d) :
    (inner ℝ P (invH Z) + inner ℝ (sandwich (invH X) P) Z) -
      (inner ℝ P (invH X) + inner ℝ (sandwich (invH X) P) X) =
      inner ℝ P (sandwich (invH X) (sandwich (Z-X) (invH Z))) := by
  rw [← inverse_remainder X Z hX hZ, inner_add_right, inner_sub_right,
    inner_sandwich, inner_sub_right]
  ring

lemma inverse_trace_gap_nonneg (P X Z : H d) (hP : P ∈ psdCone d)
    (hX : X ∈ pd d) (hZ : Z ∈ pd d) :
    inner ℝ P (invH X) + inner ℝ (sandwich (invH X) P) X ≤
      inner ℝ P (invH Z) + inner ℝ (sandwich (invH X) P) Z := by
  apply sub_nonneg.mp
  rw [inverse_trace_gap P X Z hX hZ]
  exact inner_nonneg_of_psd P _ hP
    (sandwich_psd _ _ (sandwich_psd _ _ hZ.inv.posSemidef))

lemma inverse_trace_gap_zero [NeZero d] (P X Z : H d) (hP : P ∈ pd d)
    (hX : X ∈ pd d) (hZ : Z ∈ pd d)
    (he : inner ℝ P (invH X) + inner ℝ (sandwich (invH X) P) X =
      inner ℝ P (invH Z) + inner ℝ (sandwich (invH X) P) Z) : X = Z := by
  have hz : inner ℝ P (sandwich (invH X) (sandwich (Z-X) (invH Z))) = 0 := by
    rw [← inverse_trace_gap P X Z hX hZ, he, sub_self]
  have hr := eq_zero_of_inner_pd hP
    (sandwich_psd _ _ (sandwich_psd _ _ hZ.inv.posSemidef)) hz
  have hc := congrArg (sandwich X) hr
  rw [sandwich_inverse_cancel X _ hX, sandwich_zero] at hc
  have hu := (sandwich_eq_zero_iff (Z-X) (invH Z) hZ.inv).mp hc
  exact (sub_eq_zero.mp hu).symm

end
end CurrentKS.Hermitian

end OAI

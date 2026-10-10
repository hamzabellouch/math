import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.SignedExtension

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section FullSupport
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma Admissible.positiveExtension_kernel {f : E → ι → ℝ} (hf : Admissible f)
    {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q) {w : E} (hw : ‖w‖ = 1)
    (hk : op Q w = 0) {i : ι} (hi : 0 < f w i) : positiveExtension f Q i = 0 := by
  apply le_antisymm _ (hf.positiveExtension_nonneg Q i)
  apply le_of_not_gt
  intro hp
  obtain ⟨v, ⟨x, rfl⟩, hv, hx⟩ := (hf.positiveExtension_support hQ i).mp hp
  exact hf.orthogonal _ _ hw hv (matrix_image_orthogonal_kernel hQ.isSelfAdjoint hk x) i
    ⟨hi, hx⟩

lemma Admissible.signedExtension_kernel {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) {w : E} (hw : ‖w‖ = 1)
    (hk : op A w = 0) : ∃ i, signedExtension f A i = 0 := by
  obtain ⟨i, hi⟩ := hf.support_nonempty hw
  have hi' := (mem_positiveSupport f w i).mp hi
  obtain ⟨hp, hn⟩ := matrix_parts_kernel hA hk
  refine ⟨i, ?_⟩
  simp only [signedExtension, Pi.sub_apply,
    hf.positiveExtension_kernel (CFC.posPart_nonneg A) hw hp hi',
    hf.positiveExtension_kernel (CFC.negPart_nonneg A) hw hn hi', sub_self]

lemma Admissible.signedExtension_kernel_eq_zero {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≠ 0)
    {w : E} (hk : op A w = 0) : w = 0 := by
  by_contra hw
  have hunit : ‖‖w‖⁻¹ • w‖ = 1 := by simp [norm_smul, norm_inv, hw]
  have hk' : op A (‖w‖⁻¹ • w) = 0 := by rw [map_smul, hk, smul_zero]
  obtain ⟨i, hi⟩ := hf.signedExtension_kernel hA hunit hk'
  exact hs i hi

lemma Admissible.signedExtension_fullSupport {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i ≠ 0) :
    IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hz : op A (WithLp.toLp 2 u - WithLp.toLp 2 v) = 0 := by
    rw [map_sub, Matrix.toEuclideanCLM_toLp, Matrix.toEuclideanCLM_toLp, huv, sub_self]
  have h := sub_eq_zero.mp (hf.signedExtension_kernel_eq_zero hA hs hz)
  exact WithLp.toLp_injective 2 h

omit [Nonempty ν] in
lemma matrix_psd_trace_zero {Q : Matrix ν ν ℝ} (hQ : 0 ≤ Q)
    (htrace : Matrix.trace Q = 0) : Q = 0 := by
  have hprod : (CFC.sqrt Q)ᴴ * CFC.sqrt Q = Q := by
    rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg Q).star_eq, CFC.sqrt_mul_sqrt_self Q hQ]
  have hz : CFC.sqrt Q = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    (hprod.symm ▸ htrace)
  rw [← hprod, hz]
  simp

lemma Admissible.signedExtension_negativeDefinite {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) (hs : ∀ i, signedExtension f A i < 0) :
    (-A).PosDef := by
  have hp (i : ι) : positiveExtension f A⁺ i = 0 := by
    have h := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
      (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · have hi := hs i
      simp only [signedExtension, Pi.sub_apply, h, sub_zero] at hi
      exact False.elim ((not_lt_of_ge (hf.positiveExtension_nonneg A⁺ i)) hi)
  have hzero : A⁺ = 0 := matrix_psd_trace_zero (CFC.posPart_nonneg A) (by
    rw [← hf.positiveExtension_sum (CFC.posPart_nonneg A)]
    simp [hp])
  have hneg : -A = A⁻ := by
    have h := CFC.posPart_sub_negPart A hA
    rw [hzero, zero_sub] at h
    exact (congrArg Neg.neg h).symm.trans (neg_neg A⁻)
  have hn : 0 ≤ -A := hneg ▸ CFC.negPart_nonneg A
  apply (Matrix.nonneg_iff_posSemidef.mp hn).posDef_iff_isUnit.mpr
  exact (hf.signedExtension_fullSupport hA (fun i => ne_of_lt (hs i))).neg

end FullSupport

end BorsukNine

end OAI

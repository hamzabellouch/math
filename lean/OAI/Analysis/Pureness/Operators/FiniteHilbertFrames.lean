import OAI.Analysis.Pureness.Stabilization.CompactMatrixUnits
import Mathlib.Analysis.InnerProductSpace.Orthonormal

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped InnerProductSpace
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def finiteFrameSynthesis {n : ℕ} (e : Fin n → K) : StandardHilbert →L[ℂ] K :=
  ∑ i, InnerProductSpace.rankOne ℂ (e i) (standardVector i.val)

lemma finiteFrameSynthesis_apply {n : ℕ} (e : Fin n → K) (x : StandardHilbert) :
    finiteFrameSynthesis e x = ∑ i, inner ℂ (standardVector i.val) x • e i := by
  simp [finiteFrameSynthesis]

lemma finiteFrameSynthesis_standard {n : ℕ} (e : Fin n → K) (j : Fin n) :
    finiteFrameSynthesis e (standardVector j.val) = e j := by
  simp [finiteFrameSynthesis_apply, inner_standardVector, Fin.val_inj]

variable [CompleteSpace K]

lemma finiteFrameSynthesis_adjoint {n : ℕ} (e : Fin n → K) :
    (finiteFrameSynthesis e).adjoint =
      ∑ i, InnerProductSpace.rankOne ℂ (standardVector i.val) (e i) := by
  simp [finiteFrameSynthesis, InnerProductSpace.adjoint_rankOne]

lemma finiteFrameSynthesis_adjoint_apply {n : ℕ} (e : Fin n → K) (x : K) :
    (finiteFrameSynthesis e).adjoint x = ∑ i, inner ℂ (e i) x • standardVector i.val := by
  simp [finiteFrameSynthesis_adjoint]

lemma orthonormal_standardFinite (n : ℕ) : Orthonormal ℂ (fun i : Fin n => standardVector i.val) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [inner_standardVector, Fin.val_inj]

omit [CompleteSpace K] in
theorem finiteFrameSynthesis_norm_le {n : ℕ} (e : Fin n → K) (he : Orthonormal ℂ e) :
    ‖finiteFrameSynthesis e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hnorm : ‖finiteFrameSynthesis e x‖ ^ 2 =
      ∑ i : Fin n, ‖inner ℂ (standardVector i.val) x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, finiteFrameSynthesis_apply]
    have h := he.inner_sum (fun i => inner ℂ (standardVector i.val) x)
      (fun i => inner ℂ (standardVector i.val) x) Finset.univ
    rw [h]
    simp_rw [RCLike.conj_mul, ← RCLike.ofReal_pow]
    simp only [map_sum, RCLike.ofReal_re]
  have hb := (orthonormal_standardFinite n).sum_inner_products_le x (s := Finset.univ)
  nlinarith [norm_nonneg (finiteFrameSynthesis e x), norm_nonneg x]

lemma finiteFrameSynthesis_adjoint_norm_le {n : ℕ} (e : Fin n → K) (he : Orthonormal ℂ e) :
    ‖(finiteFrameSynthesis e).adjoint‖ ≤ 1 := by
  simpa using finiteFrameSynthesis_norm_le e he

theorem finiteFrame_compression {n : ℕ} (e : Fin n → K) (T : K →L[ℂ] K) :
    (finiteFrameSynthesis e).adjoint.comp (T.comp (finiteFrameSynthesis e)) =
      ∑ i : Fin n, ∑ j : Fin n, inner ℂ (e i) (T (e j)) •
        (compactMatrixUnit i.val j.val : StandardHilbert →L[ℂ] StandardHilbert) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, finiteFrameSynthesis_apply, map_sum, map_smul,
    finiteFrameSynthesis_adjoint_apply,
    sum_apply, smul_apply, compactMatrixUnit,
    InnerProductSpace.rankOne_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
end CuntzPureness

end

end OAI

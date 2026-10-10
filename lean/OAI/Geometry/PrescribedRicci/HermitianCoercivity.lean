import Mathlib
import OAI.Geometry.PrescribedRicci.HermitianPair

namespace OAI

/-! Hermitian Coercivity. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma hermPair_single (v : n → ℂ) (i : n) :
    hermPair (1 : Matrix n n ℂ) (Pi.single i 1) v = v i := by
  simp [hermPair,dotProduct,Pi.single_apply]

lemma hermPair_dual_coordinate {K : Matrix n n ℂ} (hK : K.PosDef) (v : n → ℂ) (i : n) :
    hermPair K (K⁻¹*ᵥ Pi.single i 1) v = v i := by
  rw [hermPair_mulVec_left,hK.inv.isHermitian.eq,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr hK.det_pos.ne'),hermPair_single]

lemma component_sq_le_hermPair {K : Matrix n n ℂ} (hK : K.PosDef) (v : n → ℂ) (i : n) :
    ‖v i‖^2 ≤ (K⁻¹ i i).re*(hermPair K v v).re := by
  have he := hermPair_cauchySchwarz K hK.posSemidef (K⁻¹*ᵥ Pi.single i 1) v
  rw [hermPair_dual_coordinate hK,hermPair_dual_coordinate hK] at he
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using he

lemma norm_sq_le_hermPair {K : Matrix n n ℂ} (hK : K.PosDef) (v : n → ℂ) :
    ‖v‖^2 ≤ ‖K⁻¹‖*(hermPair K v v).re := by
  have hs := hermPair_nonneg hK.posSemidef v
  have hprod : 0 ≤ ‖K⁻¹‖*(hermPair K v v).re := mul_nonneg (norm_nonneg _) hs
  have hc (i : n) : ‖v i‖^2 ≤ ‖K⁻¹‖*(hermPair K v v).re := by
    apply (component_sq_le_hermPair hK v i).trans
    exact mul_le_mul_of_nonneg_right ((Complex.re_le_norm _).trans
      (norm_entry_le_entrywise_sup_norm (K⁻¹))) hs
  have hv : ‖v‖ ≤ Real.sqrt (‖K⁻¹‖*(hermPair K v v).re) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    exact (Real.le_sqrt (norm_nonneg _) hprod).mpr (hc i)
  have hh := sq_le_sq₀ (norm_nonneg v) (Real.sqrt_nonneg (‖K⁻¹‖*(hermPair K v v).re))
  exact (hh.mpr hv).trans_eq (Real.sq_sqrt hprod)

omit [DecidableEq n] in
lemma pair_norm_le (K : Matrix n n ℂ) (v w : n → ℂ) :
    ‖hermPair K v w‖ ≤ (Fintype.card n : ℝ)^2*‖K‖*‖v‖*‖w‖ := by
  rw [hermPair_expand]
  apply (norm_sum_le _ _).trans
  calc
    ∑ i, ‖∑ j, star (v i)*K i j*w j‖ ≤
        ∑ i : n, ∑ j : n, ‖v‖*‖K‖*‖w‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul,norm_star]
      exact mul_le_mul (mul_le_mul (norm_le_pi_norm v i)
        (norm_entry_le_entrywise_sup_norm K) (norm_nonneg _) (norm_nonneg _))
        (norm_le_pi_norm w j) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end MongeAmpere

end

end OAI

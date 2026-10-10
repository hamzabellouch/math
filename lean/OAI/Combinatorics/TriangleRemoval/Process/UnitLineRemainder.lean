import Mathlib

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace

namespace SharpTerminalLeave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unit_line_remainder (v j : E) (hv : ‖v‖ = 1) (hj : ‖j‖ = 1) :
    ‖inner ℝ v j • v‖ ≤ 1 ∧
    ‖j - inner ℝ v j • v‖ ^ 2 = 1 - (inner ℝ v j) ^ 2 ∧
    ‖j - inner ℝ v j • v‖ ≤ 1 := by
  have hb : |inner ℝ v j| ≤ 1 := by
    simpa only [hv, hj, one_mul] using abs_real_inner_le_norm v j
  have hs : ‖j - inner ℝ v j • v‖ ^ 2 = 1 - (inner ℝ v j) ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, real_inner_comm j v, norm_smul,
      Real.norm_eq_abs, hv, hj]
    rw [mul_one, one_pow, sq_abs]
    ring
  refine ⟨by simpa [norm_smul, hv, Real.norm_eq_abs] using hb, hs, ?_⟩
  have hn := norm_nonneg (j - inner ℝ v j • v)
  nlinarith [sq_nonneg (inner ℝ v j)]

theorem unit_projector_difference (v j : E) (hv : ‖v‖ = 1) (hj : ‖j‖ = 1) :
    ‖rankOne ℝ j j - rankOne ℝ v v‖ ≤ 3 * ‖j - rankOne ℝ v v j‖ := by
  let a : ℝ := inner ℝ v j
  let p : E := a • v
  have hp := unit_line_remainder v j hv hj
  change ‖p‖ ≤ 1 ∧ ‖j - p‖ ^ 2 = 1 - a ^ 2 ∧ ‖j - p‖ ≤ 1 at hp
  have heq : rankOne ℝ j j - rankOne ℝ v v =
      rankOne ℝ (j - p) j + rankOne ℝ p (j - p) +
      (a ^ 2 - 1) • rankOne ℝ v v := by
    ext x
    simp only [add_apply, sub_apply,
      smul_apply, rankOne_apply, inner_sub_left,
      real_inner_smul_left, p]
    simp only [smul_sub, smul_smul]
    module
  have habs : |a ^ 2 - 1| = ‖j - p‖ ^ 2 := by
    have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖j - p‖, hp.2.1]
    rw [abs_of_nonpos (sub_nonpos.mpr ha)]
    linarith [hp.2.1]
  change ‖rankOne ℝ j j - rankOne ℝ v v‖ ≤ 3 * ‖j - p‖
  rw [heq]
  calc
    _ ≤ ‖rankOne ℝ (j - p) j‖ + ‖rankOne ℝ p (j - p)‖ +
        ‖(a ^ 2 - 1) • rankOne ℝ v v‖ := norm_add₃_le
    _ = ‖j - p‖ + ‖p‖ * ‖j - p‖ + ‖j - p‖ ^ 2 := by
      simp only [norm_rankOne, norm_smul, Real.norm_eq_abs, hj, hv, mul_one, habs]
    _ ≤ 3 * ‖j - p‖ := by
      have hmul := mul_le_mul_of_nonneg_right hp.1 (norm_nonneg (j - p))
      have hsq := mul_le_mul_of_nonneg_left hp.2.2 (norm_nonneg (j - p))
      nlinarith

theorem projector_transfer (B : E →L[ℝ] E) (v j : E)
    (hv : ‖v‖ = 1) (hj : ‖j‖ = 1) (lam θ δ ε : ℝ)
    (hB : ‖B - lam • rankOne ℝ v v‖ ≤ θ)
    (hlam : |lam - 1| ≤ δ) (hjB : ‖B j - j‖ ≤ ε) :
    ‖B - rankOne ℝ j j‖ ≤ 4 * (θ + δ) + 3 * ε := by
  let P : E →L[ℝ] E := rankOne ℝ v v
  have hP : ‖P‖ = 1 := by simp [P, norm_rankOne, hv]
  have hBP : ‖B - P‖ ≤ θ + δ := by
    calc
      _ = ‖(B - lam • P) + (lam - 1) • P‖ := by congr 1; module
      _ ≤ ‖B - lam • P‖ + ‖(lam - 1) • P‖ := norm_add_le _ _
      _ ≤ θ + δ := by
        simpa only [norm_smul, Real.norm_eq_abs, hP, mul_one] using (add_le_add hB hlam)
  have hw : ‖j - P j‖ ≤ ε + θ + δ := by
    calc
      _ = ‖(j - B j) + (B - P) j‖ := by congr 1; simp
      _ ≤ ‖j - B j‖ + ‖(B - P) j‖ := norm_add_le _ _
      _ ≤ ε + (θ + δ) * ‖j‖ := by
        apply add_le_add
        · simpa only [norm_sub_rev] using hjB
        · exact ((B - P).le_opNorm j).trans
            (mul_le_mul_of_nonneg_right hBP (norm_nonneg j))
      _ = ε + θ + δ := by rw [hj]; ring
  have hPJ := unit_projector_difference v j hv hj
  calc
    _ = ‖(B - P) + (P - rankOne ℝ j j)‖ := by congr 1; abel
    _ ≤ ‖B - P‖ + ‖P - rankOne ℝ j j‖ := norm_add_le _ _
    _ ≤ (θ + δ) + 3 * ‖j - P j‖ := add_le_add hBP (by
      simpa only [norm_sub_rev] using hPJ)
    _ ≤ 4 * (θ + δ) + 3 * ε := by linarith

end SharpTerminalLeave

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

end
end

end OAI

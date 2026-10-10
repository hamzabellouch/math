import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

section
open scoped BigOperators Topology Matrix.Norms.L2Operator MatrixOrder

namespace SharpTerminalLeave

theorem matrix_exp_l2_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : IsSelfAdjoint A) (r s : ℝ) (hs : 0 ≤ s)
    (hlower : ∀ x ∈ spectrum ℝ A, -r ≤ x) :
    ‖NormedSpace.exp ((-s) • A)‖ ≤ Real.exp (s * r) := by
  have heq : NormedSpace.exp ((-s) • A) =
      cfc (fun x : ℝ => Real.exp ((-s) * x)) A := by
    rw [← CFC.real_exp_eq_normedSpace_exp ((isSelfAdjoint_iff.mpr rfl).smul hA)]
    rw [← cfc_smul_id (R := ℝ) (-s) A hA, ← cfc_comp Real.exp (fun x : ℝ => (-s) • x) A hA]
    rfl
  rw [heq]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by nlinarith [hlower x hx])

theorem matrix_posSemidef_exp_l2_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • P)‖ ≤ 1 := by
  have h : ∀ x ∈ spectrum ℝ P, -(0 : ℝ) ≤ x := by
    simpa only [neg_zero] using (algebraMap_le_iff_le_spectrum
      (IsSelfAdjoint.of_nonneg hP.nonneg)).mp (show algebraMap ℝ _ 0 ≤ P by simp [hP.nonneg])
  simpa only [mul_zero, Real.exp_zero] using
    matrix_exp_l2_bound P (IsSelfAdjoint.of_nonneg hP.nonneg) 0 s hs h

theorem matrix_perturbed_exp_l2_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (P R : Matrix ι ι ℝ) (hP : P.PosSemidef) (hR : IsSelfAdjoint R)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((-s) • (P + R))‖ ≤ Real.exp (s * ‖R‖) := by
  have hPR : IsSelfAdjoint (P + R) := (IsSelfAdjoint.of_nonneg hP.nonneg).add hR
  have hRlower : algebraMap ℝ (Matrix ι ι ℝ) (-‖R‖) ≤ R := by
    apply algebraMap_le_of_le_spectrum (ha := hR)
    intro x hx
    have hxnorm := spectrum.norm_le_norm_of_mem hx
    rw [Real.norm_eq_abs] at hxnorm
    exact (abs_le.mp hxnorm).1
  apply matrix_exp_l2_bound (P + R) hPR ‖R‖ s hs
  apply (algebraMap_le_iff_le_spectrum hPR).mp
  exact hRlower.trans (le_add_of_nonneg_left hP.nonneg)

end SharpTerminalLeave

end

end

end OAI

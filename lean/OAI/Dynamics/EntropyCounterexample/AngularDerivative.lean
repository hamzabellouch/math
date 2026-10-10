import Mathlib

namespace OAI

noncomputable section

namespace Problem340

section AngularFactor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_fderiv_angular_power {θ : E → ℂ} {x : E}
    (hθ : DifferentiableAt ℝ θ x) (hunit : ‖θ x‖ = 1) (k : ℕ) :
    ‖fderiv ℝ (fun y => θ y ^ k) x‖ = (k : ℝ) * ‖fderiv ℝ θ x‖ := by
  rw [fderiv_fun_pow k hθ, norm_smul, nsmul_eq_mul, norm_mul, norm_pow, hunit]
  simp

theorem norm_fderiv_cutoff_angular_power {χ θ : E → ℂ} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hθ : DifferentiableAt ℝ θ x)
    (hunit : ‖θ x‖ = 1) (k : ℕ) :
    ‖fderiv ℝ (fun y => χ y * θ y ^ k) x‖ ≤
      ‖fderiv ℝ χ x‖ + (k : ℝ) * ‖χ x‖ * ‖fderiv ℝ θ x‖ := by
  rw [fderiv_fun_mul hχ (hθ.fun_pow k)]
  calc
    _ ≤ ‖χ x • fderiv ℝ (fun y => θ y ^ k) x‖ +
        ‖θ x ^ k • fderiv ℝ χ x‖ := norm_add_le _ _
    _ = ‖fderiv ℝ χ x‖ + (k : ℝ) * ‖χ x‖ * ‖fderiv ℝ θ x‖ := by
      rw [norm_smul, norm_smul, norm_pow, hunit,
        norm_fderiv_angular_power hθ hunit k]
      ring

theorem norm_fderiv_cutoff_angular_power_le {χ θ : E → ℂ} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hθ : DifferentiableAt ℝ θ x)
    (hunit : ‖θ x‖ = 1) (hcut : ‖χ x‖ ≤ 1)
    {A B : ℝ} (hA : ‖fderiv ℝ χ x‖ ≤ A) (hB : ‖fderiv ℝ θ x‖ ≤ B)
    (k : ℕ) :
    ‖fderiv ℝ (fun y => χ y * θ y ^ k) x‖ ≤ A + (k : ℝ) * B := by
  calc
    _ ≤ ‖fderiv ℝ χ x‖ + (k : ℝ) * ‖χ x‖ * ‖fderiv ℝ θ x‖ :=
      norm_fderiv_cutoff_angular_power hχ hθ hunit k
    _ ≤ A + (k : ℝ) * B := by
      apply add_le_add hA
      calc
        _ ≤ (k : ℝ) * 1 * ‖fderiv ℝ θ x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg k)) (norm_nonneg _)
        _ ≤ (k : ℝ) * B := by
          simpa using mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg k)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem norm_cutoff_angular_power_le {χ θ : E → ℂ} {x : E}
    (hunit : ‖θ x‖ = 1) (hcut : ‖χ x‖ ≤ 1) (k : ℕ) :
    ‖χ x * θ x ^ k‖ ≤ 1 := by
  simpa [norm_mul, norm_pow, hunit] using hcut

end AngularFactor

def angularPhase (z : ℂ) : ℂ := ‖z‖⁻¹ • z

@[simp] theorem angularPhase_zero : angularPhase 0 = 0 := by
  simp [angularPhase]

theorem norm_angularPhase {z : ℂ} (hz : z ≠ 0) : ‖angularPhase z‖ = 1 := by
  rw [angularPhase, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)

theorem contDiffAt_angularPhase {z : ℂ} (hz : z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n angularPhase z := by
  exact ((contDiffAt_id.norm ℂ hz).inv (norm_ne_zero_iff.mpr hz)).smul contDiffAt_id

theorem norm_fderiv_angularPhase_le {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ angularPhase z‖ ≤ 2 / ‖z‖ := by
  have hn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    differentiableAt_id.norm ℂ hz
  have hn0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hinv := (hasDerivAt_inv hn0).comp_hasFDerivAt z hn.hasFDerivAt
  have hderiv : fderiv ℝ angularPhase z =
      ‖z‖⁻¹ • ContinuousLinearMap.id ℝ ℂ +
        ((-(‖z‖ ^ 2)⁻¹) • fderiv ℝ (fun w : ℂ => ‖w‖) z).smulRight z := by
    exact (hinv.smul (hasFDerivAt_id z)).fderiv
  rw [hderiv]
  calc
    _ ≤ ‖‖z‖⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ +
        ‖((-(‖z‖ ^ 2)⁻¹) • fderiv ℝ (fun w : ℂ => ‖w‖) z).smulRight z‖ :=
      norm_add_le _ _
    _ = 2 / ‖z‖ := by
      rw [norm_smul, ContinuousLinearMap.norm_id,
        ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_fderiv_norm hn,
        norm_neg, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖z‖)),
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
      field_simp
      norm_num

theorem contDiff_cutoff_angular_power {χ : ℂ → ℂ} {n : WithTop ℕ∞}
    (hχ : ContDiff ℝ n χ) (hzero : ∀ᶠ z in nhds (0 : ℂ), χ z = 0) (k : ℕ) :
    ContDiff ℝ n (fun z => χ z * angularPhase z ^ k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℂ => (0 : ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [hzero] with z hz
    simp [hz]
  · exact hχ.contDiffAt.mul ((contDiffAt_angularPhase hz (n := n)).pow k)

theorem norm_fderiv_cutoff_phase_power_le {χ : ℂ → ℂ} {r A : ℝ}
    (hr : 0 < r) (hχ : Differentiable ℝ χ)
    (hzero : ∀ z, ‖z‖ < r → χ z = 0)
    (hcut : ∀ z, ‖χ z‖ ≤ 1) (hA : ∀ z, ‖fderiv ℝ χ z‖ ≤ A)
    (k : ℕ) (z : ℂ) :
    ‖fderiv ℝ (fun w => χ w * angularPhase w ^ k) z‖ ≤
      A + (k : ℝ) * (2 / r) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA z)
  by_cases hz : ‖z‖ < r
  · have heq : (fun w => χ w * angularPhase w ^ k) =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).eventually_mem hz] with w hw
      simp [hzero w hw]
    rw [heq.fderiv_eq]
    rw [fderiv_const_apply, norm_zero]
    positivity
  · have hzr : r ≤ ‖z‖ := le_of_not_gt hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hzr)
    apply norm_fderiv_cutoff_angular_power_le (hχ z)
      ((contDiffAt_angularPhase hz0 (n := 1)).differentiableAt one_ne_zero)
      (norm_angularPhase hz0) (hcut z) (hA z)
    exact (norm_fderiv_angularPhase_le hz0).trans
      (div_le_div_of_nonneg_left (by norm_num) hr hzr)

theorem norm_fderiv_cutoff_phase_power_linear {χ : ℂ → ℂ} {r A : ℝ}
    (hr : 0 < r) (hχ : Differentiable ℝ χ)
    (hzero : ∀ z, ‖z‖ < r → χ z = 0)
    (hcut : ∀ z, ‖χ z‖ ≤ 1) (hA : ∀ z, ‖fderiv ℝ χ z‖ ≤ A)
    (k : ℕ) (z : ℂ) :
    ‖fderiv ℝ (fun w => χ w * angularPhase w ^ k) z‖ ≤
      (A + 2 / r) * (1 + (k : ℝ)) := by
  apply (norm_fderiv_cutoff_phase_power_le hr hχ hzero hcut hA k z).trans
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA z)
  have hkir : 0 ≤ (k : ℝ) * A := mul_nonneg (Nat.cast_nonneg k) hA0
  have hri : 0 < 2 / r := div_pos (by norm_num) hr
  nlinarith

end Problem340

end

end OAI

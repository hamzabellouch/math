import OAI.Dynamics.EntropyCounterexample.AngularDerivative

namespace OAI

noncomputable section

namespace Problem340

section RealCutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_fderiv_real_cutoff_angular_power {χ : E → ℝ} {θ : E → ℂ} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hθ : DifferentiableAt ℝ θ x)
    (hunit : ‖θ x‖ = 1) (k : ℕ) :
    ‖fderiv ℝ (fun y => χ y • θ y ^ k) x‖ ≤
      ‖fderiv ℝ χ x‖ + (k : ℝ) * ‖χ x‖ * ‖fderiv ℝ θ x‖ := by
  rw [fderiv_fun_smul hχ (hθ.fun_pow k)]
  calc
    _ ≤ ‖χ x • fderiv ℝ (fun y => θ y ^ k) x‖ +
        ‖(fderiv ℝ χ x).smulRight (θ x ^ k)‖ := norm_add_le _ _
    _ = ‖fderiv ℝ χ x‖ + (k : ℝ) * ‖χ x‖ * ‖fderiv ℝ θ x‖ := by
      rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, norm_pow, hunit,
        norm_fderiv_angular_power hθ hunit k]
      ring

theorem norm_fderiv_real_cutoff_angular_power_le {χ : E → ℝ} {θ : E → ℂ} {x : E}
    (hχ : DifferentiableAt ℝ χ x) (hθ : DifferentiableAt ℝ θ x)
    (hunit : ‖θ x‖ = 1) (hcut : ‖χ x‖ ≤ 1)
    {A B : ℝ} (hA : ‖fderiv ℝ χ x‖ ≤ A) (hB : ‖fderiv ℝ θ x‖ ≤ B)
    (k : ℕ) :
    ‖fderiv ℝ (fun y => χ y • θ y ^ k) x‖ ≤ A + (k : ℝ) * B := by
  calc
    _ ≤ ‖fderiv ℝ χ x‖ + (k : ℝ) * ‖χ x‖ * ‖fderiv ℝ θ x‖ :=
      norm_fderiv_real_cutoff_angular_power hχ hθ hunit k
    _ ≤ A + (k : ℝ) * 1 * B := by gcongr
    _ = A + (k : ℝ) * B := by ring

end RealCutoff

theorem contDiff_real_cutoff_angular_power {χ : ℂ → ℝ} {n : WithTop ℕ∞}
    (hχ : ContDiff ℝ n χ) (hzero : ∀ᶠ z in nhds (0 : ℂ), χ z = 0) (k : ℕ) :
    ContDiff ℝ n (fun z => χ z • angularPhase z ^ k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℂ => (0 : ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [hzero] with z hz
    simp [hz]
  · exact hχ.contDiffAt.smul ((contDiffAt_angularPhase hz (n := n)).pow k)

theorem norm_fderiv_real_cutoff_phase_power_le {χ : ℂ → ℝ} {r A : ℝ}
    (hr : 0 < r) (hχ : Differentiable ℝ χ)
    (hzero : ∀ z, ‖z‖ < r → χ z = 0)
    (hcut : ∀ z, ‖χ z‖ ≤ 1) (hA : ∀ z, ‖fderiv ℝ χ z‖ ≤ A)
    (k : ℕ) (z : ℂ) :
    ‖fderiv ℝ (fun w => χ w • angularPhase w ^ k) z‖ ≤
      A + (k : ℝ) * (2 / r) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA z)
  by_cases hz : ‖z‖ < r
  · have heq : (fun w => χ w • angularPhase w ^ k) =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).eventually_mem hz] with w hw
      simp [hzero w hw]
    rw [heq.fderiv_eq, fderiv_const_apply, norm_zero]
    positivity
  · have hzr : r ≤ ‖z‖ := le_of_not_gt hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hzr)
    apply norm_fderiv_real_cutoff_angular_power_le (hχ z)
      ((contDiffAt_angularPhase hz0 (n := 1)).differentiableAt one_ne_zero)
      (norm_angularPhase hz0) (hcut z) (hA z)
    exact (norm_fderiv_angularPhase_le hz0).trans
      (div_le_div_of_nonneg_left (by norm_num) hr hzr)

theorem norm_real_cutoff_phase_power_le_one {χ : ℂ → ℝ}
    (hcut : ∀ z, ‖χ z‖ ≤ 1) (k : ℕ) (z : ℂ) :
    ‖χ z • angularPhase z ^ k‖ ≤ 1 := by
  have hp : ‖angularPhase z‖ ≤ 1 := by
    by_cases hz : z = 0
    · simp [hz]
    · exact le_of_eq (norm_angularPhase hz)
  rw [norm_smul, norm_pow]
  exact (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hcut z)).trans
    (pow_le_one₀ (norm_nonneg _) hp)

theorem norm_add_fderiv_real_cutoff_phase_power_le {χ : ℂ → ℝ} {r A : ℝ}
    (hr : 0 < r) (hχ : Differentiable ℝ χ)
    (hzero : ∀ z, ‖z‖ < r → χ z = 0)
    (hcut : ∀ z, ‖χ z‖ ≤ 1) (hA : ∀ z, ‖fderiv ℝ χ z‖ ≤ A)
    (k : ℕ) (z : ℂ) :
    ‖χ z • angularPhase z ^ k‖ +
      ‖fderiv ℝ (fun w => χ w • angularPhase w ^ k) z‖ ≤
      (1 + A + 2 / r) * (1 + (k : ℝ)) := by
  have hv := norm_real_cutoff_phase_power_le_one hcut k z
  have hd := norm_fderiv_real_cutoff_phase_power_le hr hχ hzero hcut hA k z
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA z)
  have hRatio : 0 ≤ 2 / r := by positivity
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

theorem exists_real_cutoff_phase_power_bound {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hsupp : HasCompactSupport χ)
    (hzero : (0 : ℂ) ∉ tsupport χ) (hcut : ∀ z, ‖χ z‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ContDiff ℝ 1 (fun z => χ z • angularPhase z ^ k) ∧
      ∀ z : ℂ, ‖χ z • angularPhase z ^ k‖ +
        ‖fderiv ℝ (fun w => χ w • angularPhase w ^ k) z‖ ≤
        C * (1 + (k : ℝ)) := by
  obtain ⟨A, hA⟩ := (hsupp.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv one_ne_zero)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport χ).isOpen_compl.mem_nhds hzero)
  have hzeroBall : ∀ z, ‖z‖ < r → χ z = 0 := by
    intro z hz
    apply image_eq_zero_of_notMem_tsupport
    apply hball
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine ⟨1 + A + 2 / r, by positivity, ?_⟩
  intro k
  refine ⟨contDiff_real_cutoff_angular_power hχ ?_ k, ?_⟩
  · have heq := notMem_tsupport_iff_eventuallyEq.mp hzero
    filter_upwards [heq] with z hz
    exact hz
  · intro z
    exact norm_add_fderiv_real_cutoff_phase_power_le hr
      (hχ.differentiable one_ne_zero) hzeroBall hcut hA k z

end Problem340

end

end OAI

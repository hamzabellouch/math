import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousResolventMoments

namespace OAI

/-! # The full resolvent contour of the contracting remainder

Outside the norm disk the resolvent contour equals the identity. The proof
uses its large-circle limit and the annulus theorem, without assuming a
spectral decomposition.
-/

open Complex Set Filter Topology Bornology

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_lt_mem_resolvent (B : E →L[ℂ] E) {z : ℂ} (hz : ‖B‖ < ‖z‖) :
    z ∈ resolventSet ℂ B := by
  apply spectrum.mem_resolventSet_of_norm_lt_mul
  exact (mul_le_of_le_one_right (norm_nonneg B)
    (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E))).trans_lt hz

theorem circleResolventOperator_eq_one (B : E →L[ℂ] E)
    {r : ℝ} (hr : ‖B‖ < r) : circleResolventOperator B r = 1 := by
  have hr0 : 0 < r := (norm_nonneg B).trans_lt hr
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hlim : Tendsto (fun z : ℂ => B * resolvent B z) (cobounded ℂ) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := B)).mul (spectrum.resolvent_tendsto_cobounded B)
  have hlimNorm : Tendsto (fun z : ℂ => ‖B * resolvent B z‖)
      (cobounded ℂ) (𝓝 0) := by simpa only [norm_zero] using hlim.norm
  have hsmall : ∀ᶠ z : ℂ in cobounded ℂ, ‖B * resolvent B z‖ < ε :=
    hlimNorm.eventually (gt_mem_nhds hε)
  obtain ⟨M, -, hM⟩ := atTop_basis_Ioi.cobounded_of_norm.eventually_iff.mp hsmall
  let R : ℝ := max (r + 1) (M + 1)
  have hrR : r < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hMR : M < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hR0 : 0 < R := hr0.trans hrR
  have hres (z : ℂ) (hz : ‖z‖ = R) : z ∈ resolventSet ℂ B :=
    norm_lt_mem_resolvent B (hr.trans (hrR.trans_le hz.ge))
  have hEq := circleResolventOperator_eq_of_annulus B hr0 hrR.le
    (fun z hz _ => norm_lt_mem_resolvent B (hr.trans_le hz))
  have hsimple : (2 * Real.pi * I : ℂ)⁻¹ •
      (∮ z in C(0, R), z⁻¹ • (1 : E →L[ℂ] E)) = 1 := by
    rw [circleIntegral.integral_smul_const]
    have hscalar : (∮ z in C(0, R), z⁻¹) = 2 * Real.pi * I := by
      simpa only [sub_zero] using
        (circleIntegral.integral_sub_inv_of_mem_ball
          (c := (0 : ℂ)) (w := 0) (Metric.mem_ball_self hR0))
    rw [hscalar, inv_smul_smul₀ (by simp [Real.pi_ne_zero, I_ne_zero])]
  have hi : CircleIntegrable (fun z : ℂ => z⁻¹ • (1 : E →L[ℂ] E)) 0 R := by
    apply ContinuousOn.circleIntegrable hR0.le
    intro z hz
    have hzr : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by rwa [hzr])
    exact ((continuousAt_id.inv₀ hz0).smul continuousAt_const).continuousWithinAt
  have hdiff : circleResolventOperator B R - 1 =
      (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(0, R), resolvent B z - z⁻¹ • (1 : E →L[ℂ] E)) := by
    rw [circleIntegral.integral_sub (circleIntegrable_resolvent B hR0.le hres) hi,
      smul_sub, hsimple]
    rfl
  have hnorm : ‖circleResolventOperator B R - 1‖ ≤ ε := by
    rw [hdiff]
    have hb : ‖(2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(0, R), resolvent B z - z⁻¹ • (1 : E →L[ℂ] E))‖ ≤ R * (ε / R) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR0.le
      intro z hz
      have hzr : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (by rwa [hzr])
      have he : resolvent B z - z⁻¹ • (1 : E →L[ℂ] E) =
          z⁻¹ • (B * resolvent B z) := by
        rw [operator_mul_resolvent B (hres z hzr), smul_sub, inv_smul_smul₀ hz0]
      rw [he, norm_smul, norm_inv, hzr, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (hM (x := z) (by change M < ‖z‖; simpa only [hzr] using hMR)).le (inv_nonneg.mpr hR0.le)
    simpa only [mul_div_cancel₀ _ hR0.ne'] using hb
  simpa only [zero_add, hEq] using hnorm

end

end DefocusingNLS

end OAI

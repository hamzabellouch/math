import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousResolventCircle

namespace OAI

/-! # Power decay on the range of the resolvent contour operator

Resolvent moments satisfy the exact recurrence obtained by multiplying by the
time-step operator.  A circle of radius less than one therefore gives a
geometric estimate on these moments and on powers applied to the contour range.
-/

open Complex Set

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem operator_mul_resolvent (T : E →L[ℂ] E) {z : ℂ}
    (hz : z ∈ resolventSet ℂ T) :
    T * resolvent T z = z • resolvent T z - 1 := by
  have h := Ring.mul_inverse_cancel (algebraMap ℂ (E →L[ℂ] E) z - T) hz
  change (algebraMap ℂ (E →L[ℂ] E) z - T) * resolvent T z = 1 at h
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm

noncomputable def circleResolventMoment (T : E →L[ℂ] E) (r : ℝ) (n : ℕ) :
    E →L[ℂ] E :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(0, r), z ^ n • resolvent T z

omit [CompleteSpace E] in
@[simp] theorem circleResolventMoment_zero (T : E →L[ℂ] E) (r : ℝ) :
    circleResolventMoment T r 0 = circleResolventOperator T r := by
  simp only [circleResolventMoment, pow_zero, one_smul, circleResolventOperator]

theorem circleResolventMoment_succ (T : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) (n : ℕ) :
    T * circleResolventMoment T r n = circleResolventMoment T r (n + 1) := by
  have hi (j : ℕ) : CircleIntegrable (fun z : ℂ => z ^ j • resolvent T z) 0 r := by
    apply ContinuousOn.circleIntegrable hr
    intro z hz
    have hzr : ‖z‖ = r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact ((continuousAt_id.pow j).smul
      (spectrum.hasDerivAt_resolvent_const_left (hres z hzr)).continuousAt).continuousWithinAt
  have hp : CircleIntegrable (fun z : ℂ => z ^ n • (1 : E →L[ℂ] E)) 0 r := by
    exact ((continuous_id.pow n).smul continuous_const).continuousOn.circleIntegrable hr
  have hz : (∮ z in C(0, r), z ^ n • (1 : E →L[ℂ] E)) = 0 := by
    rw [circleIntegral.integral_smul_const,
      (differentiable_id.pow n).diffContOnCl.circleIntegral_eq_zero hr, zero_smul]
  have hmap := circleIntegral_map_clm
    (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) T) (hi n)
  change (∮ z in C(0, r), T * (z ^ n • resolvent T z)) =
    T * (∮ z in C(0, r), z ^ n • resolvent T z) at hmap
  unfold circleResolventMoment
  rw [mul_smul_comm, ← hmap]
  congr 1
  calc
    (∮ z in C(0, r), T * (z ^ n • resolvent T z)) =
        ∮ z in C(0, r), z ^ (n + 1) • resolvent T z - z ^ n • (1 : E →L[ℂ] E) := by
      apply circleIntegral.integral_congr hr
      intro z hz'
      have hzr : ‖z‖ = r := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz'
      dsimp only
      rw [mul_smul_comm, operator_mul_resolvent T (hres z hzr), smul_sub,
        smul_smul, pow_succ]
    _ = ∮ z in C(0, r), z ^ (n + 1) • resolvent T z := by
      rw [circleIntegral.integral_sub (hi (n + 1)) hp, hz, sub_zero]

theorem pow_mul_circleResolventOperator (T : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) (n : ℕ) :
    T ^ n * circleResolventOperator T r = circleResolventMoment T r n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, ih, circleResolventMoment_succ T hr hres]

theorem circleResolventMoment_norm_bound (T : E →L[ℂ] E) {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖circleResolventMoment T r n‖ ≤ C * r ^ n := by
  have hc : ContinuousOn (resolvent T) (Metric.sphere (0 : ℂ) r) := by
    intro z hz
    exact ((spectrum.hasDerivAt_resolvent_const_left
      (hres z (by simpa only [Metric.mem_sphere, dist_zero_right] using hz))).continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn hc
  let D := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨‖(2 * Real.pi * I : ℂ)⁻¹‖ * (2 * Real.pi * r * D), by positivity, ?_⟩
  intro n
  have hint : ‖∮ z in C(0, r), z ^ n • resolvent T z‖ ≤
      2 * Real.pi * r * (r ^ n * D) := by
    apply circleIntegral.norm_integral_le_of_norm_le_const hr
    intro z hz
    have hzr : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_smul, norm_pow, hzr]
    exact mul_le_mul_of_nonneg_left ((hB z hz).trans (le_max_left _ _)) (pow_nonneg hr n)
  calc
    ‖circleResolventMoment T r n‖ = ‖(2 * Real.pi * I : ℂ)⁻¹‖ *
        ‖∮ z in C(0, r), z ^ n • resolvent T z‖ := norm_smul _ _
    _ ≤ ‖(2 * Real.pi * I : ℂ)⁻¹‖ * (2 * Real.pi * r * (r ^ n * D)) :=
      mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ = (‖(2 * Real.pi * I : ℂ)⁻¹‖ * (2 * Real.pi * r * D)) * r ^ n := by ring

theorem pow_mul_circleResolventOperator_norm_bound (T : E →L[ℂ] E)
    {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖T ^ n * circleResolventOperator T r‖ ≤ C * r ^ n := by
  simpa only [pow_mul_circleResolventOperator T hr hres] using
    circleResolventMoment_norm_bound T hr hres

theorem powers_on_circleResolvent_fixedSpace (T : E →L[ℂ] E)
    {r : ℝ} (hr : 0 ≤ r)
    (hres : ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x : E,
      circleResolventOperator T r x = x → ‖(T ^ n) x‖ ≤ C * r ^ n * ‖x‖ := by
  obtain ⟨C, hC, hb⟩ := pow_mul_circleResolventOperator_norm_bound T hr hres
  refine ⟨C, hC, fun n x hx => ?_⟩
  calc
    ‖(T ^ n) x‖ = ‖(T ^ n * circleResolventOperator T r) x‖ := by
      change ‖(T ^ n) x‖ = ‖(T ^ n) (circleResolventOperator T r x)‖
      rw [hx]
    _ ≤ ‖T ^ n * circleResolventOperator T r‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * r ^ n * ‖x‖ := mul_le_mul_of_nonneg_right (hb n) (norm_nonneg x)

end

end DefocusingNLS

end OAI

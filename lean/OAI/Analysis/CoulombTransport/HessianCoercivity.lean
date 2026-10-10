import Mathlib

namespace OAI

universe uE uX

open Filter
open scoped Topology

namespace Problem356

/-- A quantitative lower bound on a bilinear form survives a small operator-norm
perturbation. No finite-dimensional hypothesis is needed. -/
theorem bilinear_coercive_of_norm_sub_le
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B C : E →L[ℝ] E →L[ℝ] ℝ) (a δ : ℝ)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v) (hclose : ‖C - B‖ ≤ δ) :
    ∀ v, (a - δ) * ‖v‖ ^ 2 ≤ C v v := by
  intro v
  have hv := (C - B).le_opNorm₂ v v
  have hmul : ‖C - B‖ * ‖v‖ * ‖v‖ ≤ δ * ‖v‖ ^ 2 := by
    calc
      ‖C - B‖ * ‖v‖ * ‖v‖ = ‖C - B‖ * ‖v‖ ^ 2 := by ring
      _ ≤ δ * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hclose (sq_nonneg _)
  have hdiff : |C v v - B v v| ≤ δ * ‖v‖ ^ 2 := by
    simpa only [sub_apply, Real.norm_eq_abs] using hv.trans hmul
  have hlo := (abs_le.mp hdiff).1
  have hb := hB v
  nlinarith

/-- A continuous family of coercive bilinear forms remains uniformly coercive
near the base point, with half the original lower-bound constant. -/
theorem eventually_bilinear_coercive
    {X : Type uX} {E : Type uE} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : X) (a : ℝ)
    (ha : 0 < a) (hcont : ContinuousAt B x₀)
    (hbase : ∀ v, a * ‖v‖ ^ 2 ≤ B x₀ v v) :
    ∀ᶠ x in 𝓝 x₀, ∀ v, (a / 2) * ‖v‖ ^ 2 ≤ B x v v := by
  have hnear : ∀ᶠ x in 𝓝 x₀, dist (B x) (B x₀) < a / 2 :=
    (Metric.tendsto_nhds.mp hcont.tendsto) (a / 2) (half_pos ha)
  filter_upwards [hnear] with x hx
  have h := bilinear_coercive_of_norm_sub_le (B x₀) (B x) a (a / 2) hbase
    (by rw [← dist_eq_norm (B x) (B x₀)]; exact hx.le)
  have haeq : a - a / 2 = a / 2 := by ring
  simpa only [haeq] using h

/-- In finite dimension, strict positivity of a continuous bilinear form gives
one uniform positive quadratic lower bound. -/
theorem exists_bilinear_coercivity_of_pos
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ a : ℝ, 0 < a ∧ ∀ v, a * ‖v‖ ^ 2 ≤ B v v := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    have := h
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  | inr h =>
    have := h
    obtain ⟨u, hu⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
    have hne : (Metric.sphere (0 : E) 1).Nonempty := ⟨u, by simpa using hu⟩
    have hcont : Continuous (fun v => B v v) := B.continuous.clm_apply continuous_id
    obtain ⟨w, hw, hwmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne
      hcont.continuousOn
    have hwNorm : ‖w‖ = 1 := by simpa using hw
    have hwne : w ≠ 0 := by intro hw0; simp [hw0] at hwNorm
    refine ⟨B w w, hpos w hwne, ?_⟩
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hynorm : ‖(‖v‖)⁻¹ • v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv
    have hy : (‖v‖)⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by simpa using hynorm
    have hmin : B w w ≤ B ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) := hwmin hy
    have hscale : B ((‖v‖)⁻¹ • v) ((‖v‖)⁻¹ • v) * ‖v‖ ^ 2 = B v v := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      field_simp
    have hmul := mul_le_mul_of_nonneg_right hmin (sq_nonneg ‖v‖)
    rwa [hscale] at hmul

/-- Positive definiteness is an open condition for continuous bilinear families
on finite-dimensional real normed spaces. -/
theorem eventually_bilinear_pos
    {X : Type uX} {E : Type uE} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : X)
    (hcont : ContinuousAt B x₀) (hpos : ∀ v, v ≠ 0 → 0 < B x₀ v v) :
    ∀ᶠ x in 𝓝 x₀, ∀ v, v ≠ 0 → 0 < B x v v := by
  obtain ⟨a, ha, hbase⟩ := exists_bilinear_coercivity_of_pos (B x₀) hpos
  filter_upwards [eventually_bilinear_coercive B x₀ a ha hcont hbase] with x hx
  intro v hv
  exact lt_of_lt_of_le (mul_pos (half_pos ha) (sq_pos_of_pos (norm_pos_iff.mpr hv))) (hx v)

/-- Metric-ball version of openness of positive definiteness. -/
theorem exists_ball_bilinear_pos
    {X : Type uX} {E : Type uE} [PseudoMetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : X → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : X)
    (hcont : ContinuousAt B x₀) (hpos : ∀ v, v ≠ 0 → 0 < B x₀ v v) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball x₀ r, ∀ v, v ≠ 0 → 0 < B x v v := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (eventually_bilinear_pos B x₀ hcont hpos)
  exact ⟨r, hr, fun x hx => hball hx⟩

/-- A positive-definite Hessian at a point stays positive definite on a ball
when the function is twice continuously differentiable there. -/
theorem exists_ball_hessian_pos
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (x₀ : E) (hf : ContDiffAt ℝ 2 f x₀)
    (hpos : ∀ v, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x₀ v v) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball x₀ r, ∀ v, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ f) x v v := by
  have hfirst : ContDiffAt ℝ 1 (fderiv ℝ f) x₀ := hf.fderiv_right (by norm_num)
  exact exists_ball_bilinear_pos (fderiv ℝ (fderiv ℝ f)) x₀
    (hfirst.continuousAt_fderiv (by norm_num)) hpos

end Problem356

end OAI

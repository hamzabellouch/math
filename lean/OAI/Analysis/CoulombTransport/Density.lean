import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- A nonnegative smooth compactly supported square with mass one is an
admissible density, including the extra square-root regularity. -/
theorem isSmoothCompactProbabilityDensity_sq
    {g : E3 → ℝ}
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_smooth : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hg_compact : HasCompactSupport g)
    (hg_mass : (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => (g x) ^ 2) := by
  have hsqrt : (fun x : E3 => Real.sqrt ((g x) ^ 2)) = g := by
    funext x
    exact Real.sqrt_sq (hg_nonneg x)
  refine ⟨fun x => sq_nonneg (g x), hg_smooth.pow 2, ?_, ?_, ?_, hg_mass⟩
  · simpa only [pow_two, Pi.mul_def] using hg_compact.mul_left (f := g)
  · simpa only [hsqrt] using hg_smooth
  · simpa only [hsqrt] using hg_compact

/-- Normalizing a nonnegative smooth square preserves smoothness of its square root. -/
theorem isSmoothCompactProbabilityDensity_normalized_sq
    {g : E3 → ℝ}
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_smooth : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hg_compact : HasCompactSupport g)
    (hg_mass_pos : 0 < ∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) :
    IsSmoothCompactProbabilityDensity
      (fun x => (g x / Real.sqrt (∫ y : E3, (g y) ^ 2 ∂(volume : Measure E3))) ^ 2) := by
  apply isSmoothCompactProbabilityDensity_sq
  · intro x
    exact div_nonneg (hg_nonneg x) (Real.sqrt_nonneg _)
  · exact hg_smooth.div_const _
  · simpa only [div_eq_mul_inv, Pi.mul_def] using
      hg_compact.mul_right (f' := fun _ =>
        (Real.sqrt (∫ y : E3, (g y) ^ 2 ∂(volume : Measure E3)))⁻¹)
  · simp_rw [div_pow]
    rw [integral_div, Real.sq_sqrt hg_mass_pos.le, div_self hg_mass_pos.ne']

/-- A normalized nonnegative smooth square can be placed in any positive-radius ball. -/
theorem exists_normalized_smooth_square_in_ball (c : E3) {r : ℝ} (hr : 0 < r) :
    ∃ g : E3 → ℝ,
      (∀ x, 0 ≤ g x) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g ∧
      HasCompactSupport g ∧
      tsupport g ⊆ Metric.ball c r ∧
      (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1 := by
  let b : ContDiffBump c := ⟨r / 4, r / 2, by linarith, by linarith⟩
  have hb_compact : HasCompactSupport (fun x : E3 => (b x) ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using
      b.hasCompactSupport.mul_left (f := fun x => b x)
  have hb_center : b c = 1 := by
    exact b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hm : 0 < ∫ x : E3, (b x) ^ 2 ∂(volume : Measure E3) := by
    apply (b.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := c) hb_compact (fun x => sq_nonneg (b x))
    change (b c) ^ 2 ≠ 0
    rw [hb_center]
    norm_num
  let g : E3 → ℝ := fun x => b x /
    Real.sqrt (∫ y : E3, (b y) ^ 2 ∂(volume : Measure E3))
  refine ⟨g, fun x => div_nonneg b.nonneg (Real.sqrt_nonneg _),
    b.contDiff.div_const _, ?_, ?_, ?_⟩
  · simpa only [g, div_eq_mul_inv, Pi.mul_def] using
      b.hasCompactSupport.mul_right (f' := fun _ =>
        (Real.sqrt (∫ y : E3, (b y) ^ 2 ∂(volume : Measure E3)))⁻¹)
  · have hs : tsupport g ⊆ tsupport (fun x : E3 => b x) := by
      simpa only [g, div_eq_mul_inv, Pi.mul_def] using
        (tsupport_mul_subset_left (f := fun x : E3 => b x)
          (g := fun _ => (Real.sqrt (∫ y : E3, (b y) ^ 2 ∂(volume : Measure E3)))⁻¹))
    apply hs.trans
    rw [b.tsupport_eq]
    intro x hx
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    change dist x c ≤ r / 2 at hx'
    linarith
  · dsimp only [g]
    simp_rw [div_pow]
    rw [integral_div, Real.sq_sqrt hm.le, div_self hm.ne']

end Problem356

end

end OAI

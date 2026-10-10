import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicLocalizedBump

namespace OAI

/-! Localized positive periodic densities approximate any chosen path value. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Point masses in the convex-hull argument can be replaced by actual smooth
nonnegative densities while changing their vector moments arbitrarily little. -/
theorem exists_bump_average_near {f : ℝ → E} (hf : Continuous f)
    {c ε : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Function.Periodic ψ 1 ∧
      (∀ t, 0 ≤ ψ t) ∧ (∫ t in 0..1, ψ t) = 1 ∧
      ‖(∫ t in 0..1, ψ t • f t) - f c‖ < ε := by
  let V := f ⁻¹' ball (f c) (ε / 2)
  have hV : IsOpen V := isOpen_ball.preimage hf
  have hcV : c ∈ V := mem_ball_self (by positivity)
  obtain ⟨ψ, hψ, hper, hnonneg, hmass, hsupp⟩ := exists_localized_bump hc hV hcV
  refine ⟨ψ, hψ, hper, hnonneg, hmass, ?_⟩
  have hconst : Continuous (fun t => ψ t • f c) := hψ.continuous.smul continuous_const
  have hprod : Continuous (fun t => ψ t • f t) := hψ.continuous.smul hf
  have heq : (∫ t in 0..1, ψ t • f t) - f c =
      ∫ t in 0..1, ψ t • (f t - f c) := by
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub (hprod.intervalIntegrable _ _)
      (hconst.intervalIntegrable _ _), intervalIntegral.integral_smul_const, hmass, one_smul]
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖ψ t • (f t - f c)‖ ≤ ψ t * (ε / 2) := by
    by_cases hz : ψ t = 0
    · simp [hz]
    · have htV : t ∈ V := by
        by_contra h
        exact hz (hsupp t ht h)
      have hd : ‖f t - f c‖ < ε / 2 := by
        simpa only [V, mem_preimage, mem_ball, dist_eq_norm] using htV
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
      exact mul_le_mul_of_nonneg_left hd.le (hnonneg t)
  rw [heq]
  calc
    _ ≤ ∫ t in 0..1, ψ t * (ε / 2) := by
      exact intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (Filter.Eventually.of_forall (fun t ht => hb t ⟨ht.1.le, ht.2⟩))
        ((hψ.continuous.mul_const (ε / 2)).intervalIntegrable _ _)
    _ = ε / 2 := by rw [intervalIntegral.integral_mul_const, hmass, one_mul]
    _ < ε := by linarith

end ClosedSurfaceR4.LoopDensity

end

end OAI

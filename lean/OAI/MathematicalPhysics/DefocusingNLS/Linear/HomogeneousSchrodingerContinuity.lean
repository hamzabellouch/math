import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchrodingerMultiplier
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Strong continuity of the Schrödinger Fourier multiplier -/

open Filter MeasureTheory Topology

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem norm_sq_integral (a k : ℝ) (f : HomogeneousY a k) :
    ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 ∂homogeneousFourierMeasure a k := by
  have h := real_inner_self_eq_norm_sq f
  rw [L2.inner_def] at h
  simpa only [real_inner_self_eq_norm_sq] using h.symm

theorem continuous_homogeneousSchrodingerOperator (a k : ℝ) (f : HomogeneousY a k) :
    Continuous (fun t : ℝ => homogeneousSchrodingerOperator a k t f) := by
  let μ := homogeneousFourierMeasure a k
  have hi : Integrable (fun ξ => 4 * ‖f ξ‖ ^ 2) μ := by
    have h := (Lp.memLp f).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.const_mul 4
  rw [continuous_iff_continuousAt]
  intro t₀
  let F := fun t ξ => (homogeneousSchrodingerPhase t ξ - homogeneousSchrodingerPhase t₀ ξ) * f ξ
  have hm (t : ℝ) : AEStronglyMeasurable (fun ξ => ‖F t ξ‖ ^ 2) μ :=
    (((homogeneousSchrodingerPhase_continuous t).sub
      (homogeneousSchrodingerPhase_continuous t₀)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)).norm.pow 2
  have hb (t : ℝ) (ξ : E) : ‖F t ξ‖ ^ 2 ≤ 4 * ‖f ξ‖ ^ 2 := by
    have hp : ‖homogeneousSchrodingerPhase t ξ - homogeneousSchrodingerPhase t₀ ξ‖ ≤ 2 := by
      simpa only [homogeneousSchrodingerPhase_norm, one_add_one_eq_two] using
        norm_sub_le (homogeneousSchrodingerPhase t ξ) (homogeneousSchrodingerPhase t₀ ξ)
    dsimp only [F]
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [norm_nonneg (homogeneousSchrodingerPhase t ξ - homogeneousSchrodingerPhase t₀ ξ)])
      (sq_nonneg _)
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝 t₀) (fun ξ => 4 * ‖f ξ‖ ^ 2)
    (F := fun t ξ => ‖F t ξ‖ ^ 2) (f := fun _ => (0 : ℝ))
    (Eventually.of_forall hm)
    (Eventually.of_forall fun t => ae_of_all μ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb t ξ) hi
    (ae_of_all μ fun ξ => by
      have hc : Continuous (fun t : ℝ => F t ξ) := by
        dsimp only [F, homogeneousSchrodingerPhase]
        fun_prop
      simpa only [Pi.pow_apply, F, sub_self, zero_mul, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        using (hc.norm.fun_pow 2).tendsto t₀)
  have hs : Tendsto (fun t : ℝ => ‖homogeneousSchrodingerOperator a k t f -
      homogeneousSchrodingerOperator a k t₀ f‖ ^ 2) (𝓝 t₀) (𝓝 0) := by
    have he (t : ℝ) : ‖homogeneousSchrodingerOperator a k t f -
        homogeneousSchrodingerOperator a k t₀ f‖ ^ 2 = ∫ ξ, ‖F t ξ‖ ^ 2 ∂μ := by
      rw [norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (homogeneousSchrodingerOperator a k t f)
        (homogeneousSchrodingerOperator a k t₀ f),
        homogeneousSchrodingerVector_ae a k t f,
        homogeneousSchrodingerVector_ae a k t₀ f] with ξ hsub h₁ h₂
      rw [hsub]
      change ‖homogeneousSchrodingerVector a k t f ξ -
        homogeneousSchrodingerVector a k t₀ f ξ‖ ^ 2 = _
      rw [h₁, h₂, ← sub_mul]
    simp only [he, integral_zero] at *
    exact ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hs

end DefocusingNLS

end OAI

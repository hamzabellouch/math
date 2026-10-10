import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.BlowupRate
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

namespace OAI

/-!
# From a convergent similarity orbit to pointwise blowup

Convergence of the similarity-time error, followed by the physical time change
and phase cancellation, gives the rescaled pointwise blowup limit.
-/

open Filter Topology

namespace DefocusingNLS

noncomputable def similarityTime (T t : ℝ) : ℝ := Real.log (T / (T - t))

theorem similarityTime_tendsto (T : ℝ) (hT : 0 < T) :
    Tendsto (similarityTime T) (𝓝[<] T) atTop := by
  change Tendsto (fun t : ℝ => Real.log (T / (T - t))) (𝓝[<] T) atTop
  have hb : Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Tendsto (fun _ : ℝ => T) (𝓝[<] T) (𝓝 T) := tendsto_const_nhds
      simpa using hc.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr (Set.mem_Iio.mp ht)
  have hi := hb.inv_tendsto_nhdsGT_zero
  have hr := Tendsto.const_mul_atTop hT hi
  simpa only [div_eq_mul_inv, Function.comp_def, Pi.inv_apply] using
    Real.tendsto_log_atTop.comp hr

/-- The value at the blowup center after restoring amplitude and phase. -/
noncomputable def similarityCenterValue (T a θ b : ℝ) (Q : ℂ)
    (v : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp (((θ + b * Real.log ((T - t) / T) : ℝ) : ℂ) * Complex.I) *
    ((T - t) ^ (-a) • (Q + v (similarityTime T t)))

theorem rescaled_similarityCenterValue_norm (T a θ b t : ℝ) (Q : ℂ)
    (v : ℝ → ℂ) (ht : t < T) :
    (T - t) ^ a * ‖similarityCenterValue T a θ b Q v t‖ =
      ‖Q + v (similarityTime T t)‖ := by
  simp only [similarityCenterValue, norm_mul, norm_smul, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_self, Real.exp_zero, one_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sub_pos.mpr ht).le _),
    ← mul_assoc, ← Real.rpow_add (sub_pos.mpr ht)]
  simp

/-- Convergence in similarity time yields the exact positive rescaled limit
appearing in the main theorem, provided the center profile is nonzero. -/
theorem similarityCenterValue_rescaled_limit (T a θ b : ℝ) (Q : ℂ)
    (v : ℝ → ℂ) (hT : 0 < T) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun t => (T - t) ^ a * ‖similarityCenterValue T a θ b Q v t‖)
      (𝓝[<] T) (𝓝 ‖Q‖) := by
  have hlim : Tendsto (fun t => ‖Q + v (similarityTime T t)‖)
      (𝓝[<] T) (𝓝 ‖Q‖) := by
    simpa using (tendsto_const_nhds.add (hv.comp (similarityTime_tendsto T hT))).norm
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (rescaled_similarityCenterValue_norm T a θ b t Q v ht).symm

theorem similarityCenterValue_no_left_limit (T a θ b : ℝ) (Q : ℂ)
    (v : ℝ → ℂ) (hT : 0 < T) (ha : 0 < a) (hQ : Q ≠ 0)
    (hv : Tendsto v atTop (𝓝 0)) :
    ¬ ∃ z, Tendsto (similarityCenterValue T a θ b Q v) (𝓝[<] T) (𝓝 z) := by
  exact no_left_limit_of_positive_rescaled_norm _ T a ‖Q‖ ha (norm_pos_iff.mpr hQ)
    (similarityCenterValue_rescaled_limit T a θ b Q v hT hv)

end DefocusingNLS

end OAI

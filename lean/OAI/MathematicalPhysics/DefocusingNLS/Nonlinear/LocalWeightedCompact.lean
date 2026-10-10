import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzLocalConvolution

namespace OAI

/-! # Weighted physical L² compactness from bounded local convergence -/

open MeasureTheory Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_weightedL2_of_pointwise_zero (C : ℝ) (V : E → ℂ) (hV : MemLp V 2 volume)
    (u : ℕ → C(E, ℂ)) (hu : ∀ n x, ‖u n x‖ ≤ C)
    (hpoint : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : E, ‖V x * u n x‖ ^ 2) atTop (𝓝 0) := by
  have hbound (n : ℕ) (x : E) : ‖‖V x * u n x‖ ^ 2‖ ≤ ‖V x‖ ^ 2 * C ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hu n x) 2) (sq_nonneg _)
  have hp (x : E) : Tendsto (fun n => ‖V x * u n x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_mul, mul_pow, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      ((hpoint x).norm.pow 2).const_mul (‖V x‖ ^ 2)
  have hi : Integrable (fun x => ‖V x‖ ^ 2 * C ^ 2) :=
    (hV.integrable_norm_pow (p := 2) (by norm_num)).mul_const _
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => ‖V x * u n x‖ ^ 2) volume :=
    (hV.aestronglyMeasurable.mul (u n).continuous.aestronglyMeasurable).norm.pow 2
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun x => ‖V x‖ ^ 2 * C ^ 2) hm hi (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hp)

theorem tendsto_weightedL2_of_locally_uniform_zero (C : ℝ) (V : E → ℂ) (hV : MemLp V 2 volume)
    (u : ℕ → C(E, ℂ)) (hu : ∀ n x, ‖u n x‖ ≤ C)
    (hlocal : ∀ S ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ S → ‖u n y‖ < ε) :
    Tendsto (fun n => ∫ x : E, ‖V x * u n x‖ ^ 2) atTop (𝓝 0) := by
  apply tendsto_weightedL2_of_pointwise_zero C V hV u hu
  intro x
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Eventually.of_forall (fun n => hr.trans_le (norm_nonneg _))
  · intro ε hε
    filter_upwards [hlocal ‖x‖ ε hε] with n hn
    exact hn x le_rfl

end DefocusingNLS

end OAI

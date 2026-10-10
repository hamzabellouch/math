import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeGroup
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Strong continuity of the exact whole-space free group -/

open Filter MeasureTheory Topology
open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem schwartz_polynomial_bound (ψ : 𝓢(E, ℂ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, (1 + ‖ξ‖) ^ N * ‖ψ ξ‖ ≤ C := by
  let C := 2 ^ N * (Finset.Iic (N, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ
  refine ⟨|C|, abs_nonneg C, fun ξ => ?_⟩
  have h : (1 + ‖ξ‖) ^ N * ‖ψ ξ‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (N, 0)) le_rfl le_rfl ψ ξ)
  exact h.trans (le_abs_self C)

private theorem schwartz_dilation_polynomial_bound (ψ : 𝓢(E, ℂ)) (N : ℕ)
    (C : ℝ) (hC : ∀ ξ, (1 + ‖ξ‖) ^ N * ‖ψ ξ‖ ≤ C)
    (R : ℝ) (hR : 1 / 2 ≤ R) (ξ : E) :
    (1 + ‖ξ‖) ^ N * ‖ψ (R • ξ)‖ ≤ 2 ^ N * C := by
  have hRp : 0 ≤ R := by linarith
  have hx : 1 + ‖ξ‖ ≤ 2 * (1 + ‖R • ξ‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hRp]
    nlinarith [norm_nonneg ξ]
  calc
    _ ≤ (2 * (1 + ‖R • ξ‖)) ^ N * ‖ψ (R • ξ)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hx N) (norm_nonneg _)
    _ = 2 ^ N * ((1 + ‖R • ξ‖) ^ N * ‖ψ (R • ξ)‖) := by rw [mul_pow]; ring
    _ ≤ 2 ^ N * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)

private theorem free_difference_polynomial_bound (a b s : ℝ) (ψ : 𝓢(E, ℂ))
    (N : ℕ) (C : ℝ) (hC : ∀ ξ, (1 + ‖ξ‖) ^ N * ‖ψ ξ‖ ≤ C)
    (hamp : ‖homogeneousFreeAmplitude a b s‖ ≤ 2)
    (hR : 1 / 2 ≤ Real.exp (s / 2)) (ξ : E) :
    (1 + ‖ξ‖) ^ N * ‖homogeneousFreeFourier a b s ψ ξ - ψ ξ‖ ≤
      3 * 2 ^ N * C := by
  have hd := schwartz_dilation_polynomial_bound ψ N C hC _ hR ξ
  have hi := schwartz_dilation_polynomial_bound ψ N C hC 1 (by norm_num) ξ
  simp only [one_smul] at hi
  have hnorm : ‖homogeneousFreeFourier a b s ψ ξ‖ ≤
      2 * ‖ψ (Real.exp (s / 2) • ξ)‖ := by
    rw [homogeneousFreeFourier_apply, norm_mul, norm_mul, homogeneousFreePhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_right hamp (norm_nonneg _)
  calc
    _ ≤ (1 + ‖ξ‖) ^ N *
        (‖homogeneousFreeFourier a b s ψ ξ‖ + ‖ψ ξ‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ 2 * ((1 + ‖ξ‖) ^ N * ‖ψ (Real.exp (s / 2) • ξ)‖) +
        (1 + ‖ξ‖) ^ N * ‖ψ ξ‖ := by nlinarith [pow_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖) N]
    _ ≤ 3 * 2 ^ N * C := by linarith

private theorem polynomial_bound_square (N : ℕ) (D : ℝ) (_hD : 0 ≤ D)
    (ξ : E) (v : ℂ) (hv : (1 + ‖ξ‖) ^ N * ‖v‖ ≤ D) :
    ‖v‖ ^ 2 ≤ D ^ 2 * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  let P := (1 + ‖ξ‖) ^ N
  have hP : 1 ≤ P := one_le_pow₀ (by
    change (1 : ℝ) ≤ 1 + ‖ξ‖
    exact le_add_of_nonneg_right (norm_nonneg ξ))
  have hPn : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hs : (P * ‖v‖) ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hPn.le (norm_nonneg _)) hv 2
  have hsmall : P * ‖v‖ ^ 2 ≤ D ^ 2 := by
    have hp : P ≤ P ^ 2 := by nlinarith
    have hv2 := sq_nonneg ‖v‖
    nlinarith
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  exact (le_mul_inv_iff₀ hPn).mpr (by simpa only [mul_comm] using hsmall)

theorem continuous_homogeneousFreeFourier_coordinate (a b : ℝ)
    (ψ : 𝓢(E, ℂ)) (ξ : E) :
    Continuous (fun s : ℝ => homogeneousFreeFourier a b s ψ ξ) := by
  simp only [homogeneousFreeFourier_apply]
  have hA : Continuous (homogeneousFreeAmplitude a b) := by
    unfold homogeneousFreeAmplitude
    fun_prop
  have hP : Continuous (fun s => homogeneousFreePhase s ξ) := by
    unfold homogeneousFreePhase
    fun_prop
  exact (hA.mul hP).mul (ψ.continuous.comp ((Real.continuous_exp.comp
    (continuous_id.div_const 2)).smul continuous_const))

private theorem tendsto_free_Schwartz_at_zero (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    Tendsto (fun s : ℝ => homogeneousFreeOperator a b k s ha ha1 hk
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)) (𝓝 0)
      (𝓝 (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)) := by
  let μ := homogeneousFourierMeasure a k
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  let N := μ.integrablePower
  obtain ⟨C, hC0, hC⟩ := schwartz_polynomial_bound ψ N
  let D := 3 * 2 ^ N * C
  have hD : 0 ≤ D := by positivity
  have hnear : ∀ᶠ s : ℝ in 𝓝 0,
      ‖homogeneousFreeAmplitude a b s‖ ≤ 2 ∧ 1 / 2 ≤ Real.exp (s / 2) := by
    have hA : Continuous (fun s => ‖homogeneousFreeAmplitude a b s‖) := by
      unfold homogeneousFreeAmplitude
      fun_prop
    have hR : Continuous (fun s : ℝ => Real.exp (s / 2)) := by fun_prop
    have h1 := hA.continuousAt.eventually (eventually_lt_nhds (by simp :
      ‖homogeneousFreeAmplitude a b 0‖ < 2))
    have h2 := hR.continuousAt.eventually (eventually_gt_nhds (by norm_num :
      (1 / 2 : ℝ) < Real.exp (0 / 2)))
    filter_upwards [h1, h2] with s hs ht
    exact ⟨hs.le, ht.le⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun ξ : E => D ^ 2 * (1 + ‖ξ‖) ^ (-(N : ℝ)))
    (F := fun s ξ => ‖homogeneousFreeFourier a b s ψ ξ - ψ ξ‖ ^ 2)
    (f := fun _ => (0 : ℝ))
    (by filter_upwards [] with s; exact
      (((homogeneousFreeFourier a b s ψ).continuous.sub ψ.continuous).norm.pow 2).aestronglyMeasurable)
    (by
      filter_upwards [hnear] with s hs
      exact ae_of_all μ (fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact polynomial_bound_square N D hD ξ _
          (free_difference_polynomial_bound a b s ψ N C hC hs.1 hs.2 ξ)))
    ((Measure.integrable_pow_neg_integrablePower μ).const_mul (D ^ 2))
    (ae_of_all μ (fun ξ => by
      have h : Continuous (fun s : ℝ =>
          ‖homogeneousFreeFourier a b s ψ ξ - ψ ξ‖ ^ 2) :=
        ((continuous_homogeneousFreeFourier_coordinate a b ψ ξ).sub
          continuous_const).norm.pow 2
      simpa using (h.continuousAt (x := 0)).tendsto))
  have hsq : Tendsto (fun s : ℝ => ‖homogeneousFreeOperator a b k s ha ha1 hk
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) -
        homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simpa only [homogeneousFreeOperator_on_Schwartz, ← map_sub,
      homogeneousFrequencyEmbedding_norm_sq_integral, sub_apply,
      integral_zero] using hlim
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

theorem continuous_homogeneousFreeBound (a k : ℝ) : Continuous (homogeneousFreeBound a k) := by
  unfold homogeneousFreeBound
  fun_prop

/-- Strong continuity at zero follows from the dense Schwartz core and a local uniform bound. -/
theorem tendsto_homogeneousFreeOperator_at_zero (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    Tendsto (fun s : ℝ => homogeneousFreeOperator a b k s ha ha1 hk f) (𝓝 0) (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨ψ, hψ⟩ := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).exists_dist_lt
    f (by positivity : 0 < ε / 9)
  let g := homogeneousFrequencyEmbedding a k ha ha1 hk ψ
  have hfg : ‖f - g‖ < ε / 9 := by simpa only [dist_eq_norm, g] using hψ
  have hB : ∀ᶠ s : ℝ in 𝓝 0, homogeneousFreeBound a k s < 2 :=
    (continuous_homogeneousFreeBound a k).continuousAt.eventually
      (eventually_lt_nhds (by simp [homogeneousFreeBound]))
  have hg : ∀ᶠ s : ℝ in 𝓝 0,
      dist (homogeneousFreeOperator a b k s ha ha1 hk g) g < ε / 3 :=
    (tendsto_free_Schwartz_at_zero a b k ha ha1 hk ψ).eventually
      (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [hB, hg] with s hs ht
  have hsmall : ‖homogeneousFreeOperator a b k s ha ha1 hk (f - g)‖ < 2 * (ε / 9) :=
    (homogeneousFreeOperator_norm_le a b k s ha ha1 hk (f - g)).trans_lt
      (by nlinarith [norm_nonneg (f - g)])
  calc
    _ ≤ dist (homogeneousFreeOperator a b k s ha ha1 hk f)
          (homogeneousFreeOperator a b k s ha ha1 hk g) +
        dist (homogeneousFreeOperator a b k s ha ha1 hk g) g + dist g f := by
      exact (dist_triangle _ _ _).trans (add_le_add_left (dist_triangle _ _ _) _)
    _ < 2 * (ε / 9) + ε / 3 + ε / 9 := by
      rw [dist_comm g f]
      simp only [dist_eq_norm, ← map_sub] at *
      linarith
    _ < ε := by linarith

/-- The exact whole-space free group is strongly continuous at every real time. -/
theorem continuous_homogeneousFreeOperator (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    Continuous (fun s : ℝ => homogeneousFreeOperator a b k s ha ha1 hk f) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  have hs : Tendsto (fun s : ℝ => s - s₀) (𝓝 s₀) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s - s₀) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto s₀
  have ht := (tendsto_homogeneousFreeOperator_at_zero a b k ha ha1 hk f).comp hs
  have h := ((homogeneousFreeOperator a b k s₀ ha ha1 hk).continuous.tendsto f).comp ht
  change Tendsto (fun s : ℝ => homogeneousFreeOperator a b k s ha ha1 hk f)
    (𝓝 s₀) (𝓝 (homogeneousFreeOperator a b k s₀ ha ha1 hk f))
  convert h using 1
  funext s
  change homogeneousFreeOperator a b k s ha ha1 hk f =
    homogeneousFreeOperator a b k s₀ ha ha1 hk
      (homogeneousFreeOperator a b k (s - s₀) ha ha1 hk f)
  rw [← homogeneousFreeOperator_add]
  congr 2
  ring

end DefocusingNLS

end OAI

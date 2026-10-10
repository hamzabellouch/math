import OAI.NumberTheory.JointDickman.Amplification.HalaszArithmetic
import OAI.NumberTheory.JointDickman.Counting.ComplexShortIntervalConsequences
import OAI.NumberTheory.JointDickman.Amplification.ParameterEstimates
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDistanceComparison

namespace OAI

/-! # Ordinary mean decay from the proved Halász estimate -/
namespace JointDickman
open Complex Finset Filter PublishedInputs
open scoped Topology

lemma primeDistanceSquared_nonneg (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (X t : ℝ) : 0 ≤ primeDistanceSquared f X t := by
  unfold primeDistanceSquared
  apply sum_nonneg
  intro p _
  apply div_nonneg _ (Nat.cast_nonneg p)
  apply sub_nonneg.mpr
  apply (Complex.re_le_norm _).trans
  rw [norm_mul, primeDistance_phase_norm, mul_one]
  exact hf p

lemma minimumDistance_le_primeDistance (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {X t : ℝ} (ht : |t| ≤ X) :
    minimumDistance f X ≤ primeDistanceSquared f X t := by
  unfold minimumDistance
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro y ⟨u, _, rfl⟩
    exact primeDistanceSquared_nonneg f hf X u
  · exact ⟨t, abs_le.mp ht, rfl⟩

/-- This allows the coefficients and integer cutoff to vary together. The
uniform distance hypothesis is proved for the actual nonprincipal bin data. -/
theorem halasz_mean_tendsto_zero {ι : Type*} (l : Filter ι)
    (N : ι → ℕ) (hN : Tendsto N l atTop)
    (f : ι → ArithmeticFunction ℂ) (hf : ∀ i, (f i).IsMultiplicative)
    (hnorm : ∀ i n, ‖f i n‖ ≤ 1)
    (hd : ∀ R : ℝ, ∀ᶠ i in l, ∀ t : ℝ, |t| ≤ (N i : ℝ) →
      R ≤ primeDistanceSquared (f i) (N i) t) :
    Tendsto (fun i => (∑ n ∈ Icc 1 (N i), f i n) / (N i : ℂ)) l (𝓝 0) := by
  obtain ⟨C, X₀, hC, hmean⟩ := halasz_arithmetic_mean_value
  have hNr : Tendsto (fun i => (N i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hN
  have hheight : ∀ᶠ i in l, Real.log (N i : ℝ)^8 ≤ (N i : ℝ) := by
    have hp := (log_power_div_power_tendsto_zero 8 (by norm_num : (0 : ℝ) < 1)).comp hNr
    filter_upwards [hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hN.eventually_ge_atTop 1] with i hi hNi
    simp only [Function.comp_apply, Real.rpow_ofNat, Real.rpow_one] at hi
    exact ((div_le_one (by exact_mod_cast (show 0 < N i by omega) : (0 : ℝ) < N i)).mp hi.le)
  have herr : Tendsto (fun i => Real.log (Real.log (N i : ℝ)) / Real.log (N i : ℝ)) l (𝓝 0) := by
    have hlog : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact hlog.comp (Real.tendsto_log_atTop.comp hNr)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmallR : ∀ᶠ R : ℝ in atTop, C * distanceError R < ε/2 :=
    (tendsto_distanceError.const_mul C).eventually (gt_mem_nhds (by simpa using (show 0 < ε/2 by positivity)))
  obtain ⟨R, hR0, hRsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and hsmallR).exists
  have hsmallN : ∀ᶠ i in l, C * (Real.log (Real.log (N i : ℝ)) / Real.log (N i : ℝ)) < ε/2 :=
    (herr.const_mul C).eventually (gt_mem_nhds (by simpa using (show 0 < ε/2 by positivity)))
  filter_upwards [hd R, hheight, hsmallN, hNr.eventually_ge_atTop X₀,
    hN.eventually_ge_atTop 1] with i hi hhi herri hXi hNi
  have hNi0 : (0 : ℝ) < N i := by exact_mod_cast (show 0 < N i by omega)
  have hb := hmean (N i) hXi (f i) (hf i) (hnorm i) R hR0
    (fun t ht => hi t (ht.trans hhi))
  rw [dist_eq_norm, sub_zero, norm_div, Complex.norm_natCast]
  have hdiv : ‖∑ n ∈ Icc 1 (N i), f i n‖ / (N i : ℝ) ≤
      C * (distanceError R + Real.log (Real.log (N i : ℝ))/Real.log (N i : ℝ)) := by
    apply (div_le_iff₀ hNi0).mpr
    convert hb using 1
    dsimp [distanceError]
    ring
  linarith

end JointDickman

end OAI

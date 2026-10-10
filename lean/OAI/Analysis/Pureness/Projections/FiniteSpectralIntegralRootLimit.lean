import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralRankRecovery

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteSpectralIntegral_roots_tendsto
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    Tendsto (fun k => finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M)) atTop
      (𝓝 (d (finitePositiveClass n M))) := by
  let s : ℝ≥0 := max ‖M.1‖₊ 1
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have he : Positive.smul s (Positive.normalize M) = M := by
    apply Subtype.ext
    change (s : ℝ) • ((s⁻¹ : ℝ≥0) : ℝ) • M.1 = M.1
    rw [NNReal.coe_inv, smul_smul, mul_inv_cancel₀ (show (s : ℝ) ≠ 0 by exact_mod_cast hs.ne'), one_smul]
  have hc : finitePositiveClass n (Positive.normalize M) = finitePositiveClass n M :=
    finitePositiveClass_smul n M s⁻¹ (inv_pos.mpr hs)
  have hlim := finiteSpectralIntegral_roots_tendsto_contraction d hd hlsc n (Positive.normalize M)
    (Positive.normalize_norm_le_one M)
  rw [hc] at hlim
  have hscalar := CuntzTrace.ExtendedTrace.root_scalars_tendsto_one s hs
  have h := ENNReal.Tendsto.mul hscalar (Or.inl one_ne_zero) hlim (Or.inr ENNReal.one_ne_top)
  simp only [one_mul] at h
  convert h using 1
  funext k
  nth_rw 1 [← he]
  rw [Positive.power_smul _ (Positive.rootExponent_pos k),finiteSpectralIntegral_smul d hd]

theorem finiteSpectralIntegral_root_rank
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    liminf (fun k => finiteSpectralIntegral d n (Positive.power (Positive.rootExponent k) M)) atTop =
      d (finitePositiveClass n M) :=
  (finiteSpectralIntegral_roots_tendsto d hd hlsc n M).liminf_eq

theorem regularizedFiniteDimension_integral_roots_tendsto
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    Tendsto (fun k => finiteSpectralIntegral (regularizedFiniteDimension d hd) n
      (Positive.power (Positive.rootExponent k) M)) atTop
      (𝓝 (regularizedFiniteDimension d hd (finitePositiveClass n M))) := by
  apply finiteSpectralIntegral_roots_tendsto _ (regularizedFiniteDimension_monotone d hd)
  intro m
  simpa only [regularizedFiniteDimension_eval] using finiteRegularizedValue_lowerSemicontinuous d hd m
end CuntzPureness

end

end OAI

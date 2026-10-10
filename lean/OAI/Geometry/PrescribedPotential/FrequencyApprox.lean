import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevEmbedding
import OAI.Geometry.PrescribedPotential.TruncatedRellich

namespace OAI

/-! Frequency Approx. -/

section

 

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped BoundedContinuousFunction SchwartzMap Classical ContDiff
namespace EllipticCompact
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
open SobolevChart

omit [FiniteDimensional ℝ E] in
lemma inverseWeight_one_apply (x : E) :
    inverseWeight 1 x = ((((1 + ‖x‖ ^ 2 : ℝ)⁻¹) : ℝ) : ℂ) := by
  change (((1 + ‖x‖ ^ 2) ^ (-((1 : ℕ) : ℝ)) : ℝ) : ℂ) = _
  rw [Nat.cast_one, Real.rpow_neg_one]

omit [FiniteDimensional ℝ E] in
lemma inverseWeight_one_norm (x : E) :
    ‖inverseWeight 1 x‖ = 1 / (1 + ‖x‖ ^ 2) := by
  rw [inverseWeight_one_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity)), one_div]

def frequencyBump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := (n : ℝ) + 1
  rOut := (n : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

lemma frequencyCutoff_support (n : ℕ) :
    HasCompactSupport (fun x : E => (frequencyBump (E := E) n x : ℂ) * inverseWeight 1 x) := by
  have hb : HasCompactSupport (fun x : E => (frequencyBump (E := E) n x : ℂ)) :=
    (frequencyBump (E := E) n).hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  exact hb.mul_right

def frequencyCutoff (n : ℕ) : 𝓢(E, ℂ) := (frequencyCutoff_support (E := E) n).toSchwartzMap
  ((Complex.ofRealCLM.contDiff.comp (frequencyBump (E := E) n).contDiff).mul (inverseWeight_temperate 1).1)

lemma frequencyCutoff_apply (n : ℕ) (x : E) :
    frequencyCutoff (E := E) n x = (frequencyBump (E := E) n x : ℂ) * inverseWeight 1 x := rfl

lemma frequencyCutoff_compact (n : ℕ) : HasCompactSupport (frequencyCutoff (E := E) n) :=
  frequencyCutoff_support n

lemma frequencyCutoff_bound (n : ℕ) :
    ‖(frequencyCutoff (E := E) n).toBoundedContinuousFunction - inverseWeight 1‖ ≤
      1 / ((n : ℝ) + 1) := by
  apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ 1 / ((n : ℝ) + 1))).mpr
  intro x
  change ‖frequencyCutoff (E := E) n x - inverseWeight 1 x‖ ≤ _
  rw [frequencyCutoff_apply]
  by_cases hx : ‖x‖ ≤ (n : ℝ) + 1
  · have hx' : x ∈ Metric.closedBall (0 : E) (frequencyBump (E := E) n).rIn := by
      simpa only [Metric.mem_closedBall, dist_zero_right, frequencyBump] using hx
    rw [(frequencyBump (E := E) n).one_of_mem_closedBall hx', Complex.ofReal_one, one_mul,
      sub_self, norm_zero]
    positivity
  · have hR : 0 < (n : ℝ) + 1 := by positivity
    have hx' : (n : ℝ) + 1 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
    have hden : (n : ℝ) + 1 ≤ 1 + ‖x‖ ^ 2 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [norm_nonneg x]
    have hb' : ‖(frequencyBump (E := E) n x : ℂ) - 1‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(frequencyBump (E := E) n).nonneg' x],
        by linarith [(frequencyBump (E := E) n).le_one (x := x)]⟩
    calc
      _ = ‖((frequencyBump (E := E) n x : ℂ) - 1) * inverseWeight 1 x‖ := by congr 1; ring
      _ = ‖(frequencyBump (E := E) n x : ℂ) - 1‖ * ‖inverseWeight 1 x‖ := norm_mul _ _
      _ ≤ 1 * ‖inverseWeight 1 x‖ := mul_le_mul_of_nonneg_right hb' (norm_nonneg _)
      _ ≤ 1 / ((n : ℝ) + 1) := by
        rw [one_mul, inverseWeight_one_norm]
        exact one_div_le_one_div_of_le hR hden

lemma inverseWeight_schwartz_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ χ : 𝓢(E, ℂ), HasCompactSupport χ ∧
      ‖χ.toBoundedContinuousFunction - inverseWeight 1‖ < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact ⟨frequencyCutoff n, frequencyCutoff_compact n, (frequencyCutoff_bound n).trans_lt hn⟩

variable [MeasurableSpace E] [BorelSpace E]

lemma multiply_sub (g h : E →ᵇ ℂ) : multiply (g-h) = multiply g - multiply h := by
  ext1 u
  apply Lp.ext
  filter_upwards [multiply_ae (g-h) u, multiply_ae g u, multiply_ae h u,
    Lp.coeFn_sub (multiply g u) (multiply h u)] with x h₁ h₂ h₃ h₄
  change (multiply (g-h) u : E → ℂ) x = ((multiply g u - multiply h u : L2 E) : E → ℂ) x
  rw [h₁, h₄, Pi.sub_apply, h₂, h₃]
  simp only [BoundedContinuousFunction.sub_apply, sub_mul]

lemma multiplier_sub (g h : E →ᵇ ℂ) : multiplier (g-h) = multiplier g - multiplier h := by
  ext1 u
  simp only [multiplier, ContinuousLinearMap.comp_apply, multiply_sub,
    sub_apply, map_sub]

lemma localized_multiplier_diff_bound (κ g h : E →ᵇ ℂ) :
    ‖multiply κ ∘L multiplier g - multiply κ ∘L multiplier h‖ ≤ ‖κ‖ * ‖g-h‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  rw [← map_sub]
  have he : multiplier g u - multiplier h u = multiplier (g-h) u := by
    rw [multiplier_sub, sub_apply]
  rw [he]
  calc
    ‖multiply κ (multiplier (g-h) u)‖ ≤ ‖κ‖ * ‖multiplier (g-h) u‖ := multiply_norm_le _ _
    _ ≤ ‖κ‖ * (‖g-h‖ * ‖u‖) := mul_le_mul_of_nonneg_left (multiplier_norm_le _ _) (norm_nonneg _)
    _ = _ := by ring

lemma compact_localized_frequency (κ χ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport κ) (hχ : HasCompactSupport χ) :
    IsCompactOperator (multiply κ.toBoundedContinuousFunction ∘L
      multiplier χ.toBoundedContinuousFunction) := by
  have h := (compact_truncated κ χ hκ hχ).comp_clm (fourierCLM ℂ (L2 E))
  simpa only [multiplier, ContinuousLinearMap.coe_comp, Function.comp_assoc] using h

lemma localized_frequency_distance (κ χ : 𝓢(E, ℂ)) {ε : ℝ}
    (happ : ‖χ.toBoundedContinuousFunction - inverseWeight 1‖ <
      ε / (‖κ.toBoundedContinuousFunction‖ + 1)) :
    dist (multiply κ.toBoundedContinuousFunction ∘L multiplier (inverseWeight 1))
      (multiply κ.toBoundedContinuousFunction ∘L multiplier χ.toBoundedContinuousFunction) < ε := by
  have hB : 0 < ‖κ.toBoundedContinuousFunction‖ + 1 := by positivity
  rw [dist_comm, dist_eq_norm]
  calc
    _ ≤ ‖κ.toBoundedContinuousFunction‖ * ‖χ.toBoundedContinuousFunction - inverseWeight 1‖ :=
      localized_multiplier_diff_bound _ _ _
    _ ≤ (‖κ.toBoundedContinuousFunction‖ + 1) * ‖χ.toBoundedContinuousFunction - inverseWeight 1‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (‖κ.toBoundedContinuousFunction‖ + 1) * (ε / (‖κ.toBoundedContinuousFunction‖ + 1)) :=
      mul_lt_mul_of_pos_left happ hB
    _ = ε := mul_div_cancel₀ _ (ne_of_gt hB)

 
theorem localized_bessel_compact (κ : 𝓢(E, ℂ)) (hκ : HasCompactSupport κ) :
    IsCompactOperator (multiply κ.toBoundedContinuousFunction ∘L multiplier (inverseWeight 1)) := by
  have hc : IsClosed {T : L2 E →L[ℂ] L2 E | IsCompactOperator T} :=
    isClosed_setOfPred_isCompactOperator
  change (multiply κ.toBoundedContinuousFunction ∘L multiplier (inverseWeight 1)) ∈
    {T : L2 E →L[ℂ] L2 E | IsCompactOperator T}
  rw [← hc.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hB : 0 < ‖κ.toBoundedContinuousFunction‖ + 1 := by positivity
  obtain ⟨χ, hχ, happ⟩ := inverseWeight_schwartz_approx (E := E) (div_pos hε hB)
  exact ⟨multiply κ.toBoundedContinuousFunction ∘L multiplier χ.toBoundedContinuousFunction,
    compact_localized_frequency κ χ hκ hχ, localized_frequency_distance κ χ happ⟩

end EllipticCompact

end
end

end OAI

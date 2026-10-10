import OAI.Geometry.NodalSets.Charts.MetricNormalizationStabilityLemmas
import OAI.Geometry.NodalSets.Elliptic.CorrugationFrequencyScale
import OAI.Geometry.NodalSets.Elliptic.CorrugationGradientFreezing
import OAI.Geometry.NodalSets.Elliptic.CorrugationLeadingLength

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def corrugationGradientRate (L : ℝ) (k : ℕ) : ℝ :=
  corrugationScale L k+1/(corrugationFrequency k*corrugationScale L k)

lemma corrugationGradientRate_positive {L : ℝ} (hL : 0 < L) (k : ℕ) :
    0 < corrugationGradientRate L k := by
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  unfold corrugationGradientRate
  positivity

lemma corrugationGradientRate_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (corrugationGradientRate L) atTop (𝓝 0) := by
  change Tendsto (fun k ↦ corrugationScale L k+1/(corrugationFrequency k*corrugationScale L k)) atTop (𝓝 0)
  simpa only [one_div,add_zero,Pi.inv_apply] using (corrugationScale_tendsto L).add
    (corrugation_frequency_scale_tendsto hL).inv_tendsto_atTop

theorem corrugation_normalized_gradient_freezing
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : Coord ≃L[ℝ] Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ‖metricNormalize (g x) (metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x) -
        metricNormalize (g y) (corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e
          (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y)))‖ ≤
        C*corrugationGradientRate L k := by
  obtain ⟨A,hA,hgrad⟩ := corrugation_gradient_freezing g S χ hD hconv hU hDU hg hS hp hn hχ hc hχ0 hχ1 ha ha1
  obtain ⟨c,hc0,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  obtain ⟨G,hG,hfreeze⟩ := smooth_compact_freezing g hD hconv hU hDU hg
  let K : ℝ := 5*(1+c⁻¹)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨ε₀,B,hε₀,hB,hstab⟩ := metric_normalization_uniform_stability hM.le hK
  let Q : ℝ := A+G+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨B*Q,mul_pos hB hQ,?_⟩
  have ht : Tendsto (fun k ↦ Q*corrugationGradientRate L k) atTop (𝓝 0) :=
    by simpa using (corrugationGradientRate_tendsto hL).const_mul Q
  filter_upwards [ht.eventually_lt_const hε₀] with k hk
  intro y hy x hx hxy e he0 he
  let s := corrugationOldSlope g S y
  let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp) s
    (corrugationFrequency k) (corrugationScale L k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
  let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e
    (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
  have hs := corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy)
  have hρ := (corrugationGradientRate_positive hL k).le
  have hJ := corrugationFrequency_positive k
  have hR := corrugationScale_positive hL k
  have hr : corrugationScale L k ≤ corrugationGradientRate L k := by
    dsimp [corrugationGradientRate]
    have hh : 0 ≤ 1/(corrugationFrequency k*corrugationScale L k) := by positivity
    linarith
  have hraw : ‖p-s • w‖ ≤ s*(A*corrugationGradientRate L k) := by
    simpa only [p,w,s,corrugationGradientRate,mul_assoc] using hgrad _ _ hJ hR y hy x hx hxy e he0 he
  have hd : ‖s⁻¹ • p-w‖ ≤ Q*corrugationGradientRate L k := by
    apply (inverse_scaled_vector_error p w hs hraw).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) hρ
  have hm : ‖g x-g y‖ ≤ Q*corrugationGradientRate L k := by
    calc
      _ ≤ G*‖x-y‖ := hfreeze x hx y hy
      _ ≤ G*corrugationGradientRate L k := mul_le_mul_of_nonneg_left (hxy.trans hr) hG.le
      _ ≤ Q*corrugationGradientRate L k := mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith) hρ
  have hw : ‖w‖ ≤ K := corrugationLeadingVector_bound (g y) hc0 (hmetric y hy).2 ha ha1
    (hχ0 _) (hχ1 _) e he _
  have hlen : 1 ≤ g y w w := corrugationLeadingVector_length_ge_one (g y) e he amp _ _
  have hh := (hstab (g x) (g y) (s⁻¹ • p) w (Q*corrugationGradientRate L k)
    (hmetric x hx).1 hw hlen hd hm hk.le).2.2
  rw [metricNormalize_positive_smul (g x) p (inv_pos.mpr hs)] at hh
  convert hh using 1
  ring

end
end Yau.Geometry

end OAI

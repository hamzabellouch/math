import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Radial.CapCosts

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace CylinderCovering.HalfheightFinite

theorem height_pos : 0 < height := by
  unfold height
  positivity

theorem limitingArea_eq_Q (δ : ℝ) (R : ℝ → ℝ) :
    limitingArea δ R = height / 4 * RadialCaps.Q (fun r => 2 * R r) (δ / 2) := by
  have hD (r : ℝ) :
      1 + (δ / 2) ^ 2 * RadialCaps.D0 r =
        1 + δ ^ 2 * (alpha r ^ 2 + 2 * beta r ^ 2) := by
    unfold RadialCaps.D0 RadialCaps.G alpha beta
    ring
  have hQ : RadialCaps.Q (fun r => 2 * R r) (δ / 2) =
      2 * ∫ r in (-1 : ℝ)..1,
        R r ^ 2 / Real.sqrt (1 + δ ^ 2 * (alpha r ^ 2 + 2 * beta r ^ 2)) := by
    unfold RadialCaps.Q
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only
    rw [hD]
    ring
  rw [hQ]
  unfold limitingArea
  ring

theorem cubic_cap_dictionary (δ r : ℝ) :
    2 * cubicCap δ r = RadialCaps.cubicCap 64 (δ / 2) r := by
  unfold cubicCap profile RadialCaps.cubicCap RadialCaps.H
  ring

theorem fractional_power_dictionary {δ : ℝ} (hδ : 0 < δ) :
    (8 * Real.sqrt 2) * (δ / 2) ^ (5 / 2 : ℝ) = 2 * δ ^ (5 / 2 : ℝ) := by
  rw [RadialCaps.rpow_five_halves hδ,
    RadialCaps.rpow_five_halves (show 0 < δ / 2 by positivity), Real.sqrt_div hδ.le]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  ring

theorem fractional_cap_dictionary {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    2 * fractionalCap δ r =
      RadialCaps.fractionalCap (8 * Real.sqrt 2) (δ / 2) r := by
  unfold fractionalCap profile RadialCaps.fractionalCap RadialCaps.H
  rw [fractional_power_dictionary hδ]
  ring

theorem limitingArea_cubic_eq_Q (δ : ℝ) :
    limitingArea δ (cubicCap δ) =
      height / 4 * RadialCaps.Q (RadialCaps.cubicCap 64 (δ / 2)) (δ / 2) := by
  rw [limitingArea_eq_Q]
  congr 2
  funext r
  exact cubic_cap_dictionary δ r

theorem limitingArea_fractional_eq_Q {δ : ℝ} (hδ : 0 < δ) :
    limitingArea δ (fractionalCap δ) =
      height / 4 * RadialCaps.Q
        (RadialCaps.fractionalCap (8 * Real.sqrt 2) (δ / 2)) (δ / 2) := by
  rw [limitingArea_eq_Q]
  congr 2
  funext r
  exact fractional_cap_dictionary hδ r

theorem half_tendsto_right :
    Tendsto (fun δ : ℝ => δ / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun δ : ℝ => δ / 2) 0 := by fun_prop
    simpa only [zero_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0 < δ / 2
    exact div_pos hδ (by norm_num)

theorem cubic_cost_bigO :
    (fun δ => limitingArea δ (cubicCap δ) -
      height / 2 * (1 / 2 - δ ^ 2 / 240 + 8 * δ ^ 3))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 4) := by
  have h := ((RadialCaps.cubic_cost_bigO (by norm_num : (0 : ℝ) ≤ 64)).comp_tendsto
    half_tendsto_right).const_mul_left (height / 4)
  have h' : (fun δ => limitingArea δ (cubicCap δ) -
      height / 2 * (1 / 2 - δ ^ 2 / 240 + 8 * δ ^ 3))
      =O[𝓝[>] (0 : ℝ)] (fun δ => (1 / 16 : ℝ) * δ ^ 4) :=
    h.congr (fun δ => by
    dsimp [Function.comp]
    rw [limitingArea_cubic_eq_Q]
    ring) (fun δ => show (δ / 2) ^ 4 = (1 / 16 : ℝ) * δ ^ 4 by ring)
  exact h'.of_const_mul_right

theorem fractional_cost_bigO :
    (fun δ => limitingArea δ (fractionalCap δ) -
      height / 2 * (1 / 2 - δ ^ 2 / 240 + 2 * δ ^ (5 / 2 : ℝ)))
      =O[𝓝[>] (0 : ℝ)] (fun δ => δ ^ 4) := by
  have h := ((RadialCaps.fractional_cost_bigO
    (by positivity : (0 : ℝ) ≤ 8 * Real.sqrt 2)).comp_tendsto
    half_tendsto_right).const_mul_left (height / 4)
  have he : (fun δ => height / 4 *
      (RadialCaps.Q (RadialCaps.fractionalCap (8 * Real.sqrt 2) (δ / 2)) (δ / 2) -
        (1 - (δ / 2) ^ 2 / 30 + 2 * (8 * Real.sqrt 2) * (δ / 2) ^ (5 / 2 : ℝ))))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun δ => limitingArea δ (fractionalCap δ) -
        height / 2 * (1 / 2 - δ ^ 2 / 240 + 2 * δ ^ (5 / 2 : ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0 < δ at hδ
    rw [limitingArea_fractional_eq_Q hδ]
    have hp := fractional_power_dictionary hδ
    rw [show 2 * (8 * Real.sqrt 2) * (δ / 2) ^ (5 / 2 : ℝ) =
      4 * δ ^ (5 / 2 : ℝ) by linarith only [hp]]
    ring
  have h' := h.congr' he (Filter.Eventually.of_forall
    (fun δ => show (δ / 2) ^ 4 = (1 / 16 : ℝ) * δ ^ 4 by ring))
  exact h'.of_const_mul_right

theorem limiting_costs_strict :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      limitingArea δ (cubicCap δ) < height / 4 ∧
      limitingArea δ (fractionalCap δ) < height / 4 := by
  filter_upwards [half_tendsto_right.eventually
      (RadialCaps.cubic_cost_strict (by norm_num : (0 : ℝ) ≤ 64)),
    half_tendsto_right.eventually
      (RadialCaps.fractional_cost_strict (by positivity : (0 : ℝ) ≤ 8 * Real.sqrt 2)),
    self_mem_nhdsWithin] with δ hc hf hδ
  change 0 < δ at hδ
  rw [limitingArea_cubic_eq_Q, limitingArea_fractional_eq_Q hδ]
  constructor
  · nlinarith [height_pos]
  · nlinarith [height_pos]

theorem finite_saving_of_convergence {δ : ℝ} {R : ℝ → ℝ}
    (hconv : Tendsto (totalArea δ R) atTop (𝓝 (limitingArea δ R)))
    (hlt : limitingArea δ R < height / 4) :
    ∀ᶠ N in atTop, 0 < N ∧ totalArea δ R N < height / 4 := by
  exact (eventually_gt_atTop (0 : ℕ)).and (hconv.eventually (gt_mem_nhds hlt))

theorem eventual_finite_saving
    (hc : ∀ᶠ δ : ℝ in 𝓝[>] 0, FamilyConclusion δ (cubicCap δ))
    (hf : ∀ᶠ δ : ℝ in 𝓝[>] 0, FamilyConclusion δ (fractionalCap δ)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (∀ᶠ N in atTop, 0 < N ∧ totalArea δ (cubicCap δ) N < height / 4) ∧
      (∀ᶠ N in atTop, 0 < N ∧ totalArea δ (fractionalCap δ) N < height / 4) := by
  filter_upwards [hc, hf, limiting_costs_strict] with δ hδc hδf hlt
  exact ⟨finite_saving_of_convergence hδc.2 hlt.1,
    finite_saving_of_convergence hδf.2 hlt.2⟩

end CylinderCovering.HalfheightFinite

end

end OAI

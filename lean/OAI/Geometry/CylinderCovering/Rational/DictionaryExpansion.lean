import OAI.Geometry.CylinderCovering.Rational.DictionaryExpansionDefinitions
import OAI.Geometry.CylinderCovering.Rational.DictionaryCoefficients
import OAI.Geometry.CylinderCovering.Rational.CostActual
import OAI.Geometry.CylinderCovering.Rational.Asymptotic

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace RationalDictionary

lemma uncenteredQuadraticCoefficient_eq (d0 eta0 : ℝ) :
    uncenteredQuadraticCoefficient d0 eta0 =
      uncenteredCeiling d0 + 2 * c0 * eta0 - uncenteredEnergy d0 := by
  unfold uncenteredQuadraticCoefficient uncenteredCeiling
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  · apply Continuous.intervalIntegrable
    unfold a0 A0 B0
    fun_prop
  · exact intervalIntegrable_const

lemma coefficientFactor_eq (d0 : ℝ) :
    32 * (1 + d0) ^ 2 / ell = 128 * c0 * (1 + d0) ^ 2 := by
  apply (div_eq_iff ell_ne_zero).mpr
  calc
    32 * (1 + d0) ^ 2 = 128 * (ell * c0) * (1 + d0) ^ 2 := by
      rw [ell_mul_c0]
      ring
    _ = 128 * c0 * (1 + d0) ^ 2 * ell := by ring

lemma uncentered_remainder_dictionary {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    orthonormalCost d0 eta0 k - (c0 + k ^ 2 * uncenteredQuadraticCoefficient d0 eta0) =
      (8 * c0) *
        (SlopeRational.weightedCost (d0 / 2) (centeredTilt d0 k) (centeredPadding eta0 k) /
          SlopeRational.physicalScale -
        (1 / 8 + centeredTilt d0 k ^ 2 *
          (SlopeRational.ceilingIntegral (d0 / 2) - SlopeRational.energyIntegral (d0 / 2)) +
          centeredPadding eta0 k / 2)) := by
  rw [uncenteredQuadraticCoefficient_eq, energy_dictionary hd,
    ceiling_dictionary_integral hd, coefficientFactor_eq]
  rw [show d0 / 2 = centeredRegularization d0 from rfl,
    CostTransfer.weightedCost_dictionary hd]
  change _ = (8 * c0) * (orthonormalCost d0 eta0 k / 8 / c0 - _)
  unfold centeredTilt centeredPadding
  field_simp [ne_of_gt c0_pos]
  ring

theorem uncenteredCost_expansion {d0 eta0 : ℝ} (hd : 0 < d0) (he : 0 ≤ eta0) :
    IsBigO (𝓝[>] (0 : ℝ))
      (fun k => orthonormalCost d0 eta0 k -
        (c0 + k ^ 2 * uncenteredQuadraticCoefficient d0 eta0)) (fun k => k ^ 4) := by
  let Q := centeredMargin d0 eta0
  let A := 4 * (1 + d0)
  let B := ((3 / 8 : ℝ) * (3 / 64) ^ 2 * (3 / 8) +
    (3 / 64) * (1 + Q) / 2 + (1 + Q) ^ 2)
  have hQ : 0 ≤ Q := by dsimp [Q, centeredMargin]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hlim : Tendsto (fun k : ℝ => centeredTilt d0 k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun k : ℝ => centeredTilt d0 k) 0 := by
      unfold centeredTilt
      fun_prop
    simpa [centeredTilt] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hδ : 0 < 1 / (4 * (1 + Q)) := by positivity
  apply IsBigO.of_bound (8 * c0 * B * A ^ 4)
  filter_upwards [self_mem_nhdsWithin, hlim.eventually (gt_mem_nhds hδ)] with k hk hsmall
  have hk0 : 0 < k := hk
  have heps : 0 ≤ centeredTilt d0 k := by unfold centeredTilt; positivity
  have hpad : 0 ≤ centeredPadding eta0 k := by unfold centeredPadding; positivity
  have heq : centeredPadding eta0 k = Q * centeredTilt d0 k ^ 2 :=
    centeredPadding_eq_margin_mul_tilt_sq (by positivity) eta0 k
  have hb := SlopeRational.weightedCost_expansion_bound
    (show 0 < d0 / 2 by positivity) hQ heps hsmall.le hpad heq.le
  rw [uncentered_remainder_dictionary hd]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos c0_pos, abs_of_pos (show (0 : ℝ) < 8 by norm_num),
    abs_of_nonneg (show 0 ≤ k ^ 4 by positivity)]
  calc
    8 * c0 * |SlopeRational.weightedCost (d0 / 2) (centeredTilt d0 k)
        (centeredPadding eta0 k) / SlopeRational.physicalScale -
        (1 / 8 + centeredTilt d0 k ^ 2 *
          (SlopeRational.ceilingIntegral (d0 / 2) - SlopeRational.energyIntegral (d0 / 2)) +
          centeredPadding eta0 k / 2)| ≤ 8 * c0 * (B * centeredTilt d0 k ^ 4) :=
      mul_le_mul_of_nonneg_left hb (by have hc := c0_pos; positivity)
    _ = 8 * c0 * B * A ^ 4 * k ^ 4 := by dsimp [A, centeredTilt]; ring

lemma uncenteredCost_eventually_lt {d0 eta0 : ℝ}
    (hd : 0 < d0) (he : 0 < eta0) (heta : eta0 < coefficientGap d0 / (2 * c0)) :
    ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ), orthonormalCost d0 eta0 k < c0 := by
  have hc : uncenteredQuadraticCoefficient d0 eta0 < 0 := by
    rw [uncenteredQuadraticCoefficient_eq]
    have hmul := (lt_div_iff₀ (mul_pos (by norm_num) c0_pos)).mp heta
    unfold coefficientGap at hmul
    nlinarith
  apply SlopeRational.eventually_lt_of_quadratic_expansion hc
  have h := SlopeRational.fourth_order_implies_quadratic_littleO
    (uncenteredCost_expansion hd he.le)
  convert h using 1
  funext k
  congr 1
  ring

lemma exists_uncenteredCost_saving :
    ∃ d0 : ℝ, 0 < d0 ∧ ∃ eta0 : ℝ, 0 < eta0 ∧
      eta0 < coefficientGap d0 / (2 * c0) ∧
      ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ), orthonormalCost d0 eta0 k < c0 := by
  obtain ⟨d0, hd, hgap⟩ := exists_positive_coefficientGap
  let eta0 := coefficientGap d0 / (4 * c0)
  have he : 0 < eta0 := by dsimp [eta0]; exact div_pos hgap (mul_pos (by norm_num) c0_pos)
  have heta : eta0 < coefficientGap d0 / (2 * c0) := by
    dsimp [eta0]
    apply div_lt_div_of_pos_left hgap
    · exact mul_pos (by norm_num) c0_pos
    · have hc := c0_pos; linarith
  exact ⟨d0, hd, eta0, he, heta, uncenteredCost_eventually_lt hd he heta⟩

theorem uncentered_expansion : UncenteredExpansionStatement := by
  refine ⟨fun _ hd _ he => uncenteredCost_expansion hd he, ?_, exists_uncenteredCost_saving⟩
  intro d0 hd _ eta0 he heta
  exact uncenteredCost_eventually_lt hd he heta

end RationalDictionary

end

end OAI

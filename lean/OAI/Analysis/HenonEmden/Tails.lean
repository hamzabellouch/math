import OAI.Analysis.HenonEmden.PressureRecovery

namespace OAI

universe uE

section Tails

open MeasureTheory Set Filter
open scoped ENNReal
namespace HenonLaneEmden.UniformTail

lemma dyadic_power_identity {R : ℝ} (hR : 0 < R) (a s C : ℝ) (k : ℕ) :
    (R*2^k)^(-a) * (C*(R*2^(k+1))^s) =
      (C*2^s*R^(s-a)) * (2^(s-a))^k := by
  rw [show (2:ℝ)^(k+1) = 2*2^k by rw [pow_succ]; ring,
    show R*(2*2^k) = (2*R)*2^k by ring,
    Real.mul_rpow hR.le (by positivity),Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by norm_num) hR.le,
    ← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2) (-a) k,
    ← Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2) s k]
  rw [show R^(s-a) = R^(-a)*R^s by rw [← Real.rpow_add hR]; congr 1; ring,
    show (2:ℝ)^(s-a) = 2^(-a)*2^s by rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 1; ring,
    mul_pow]
  ring

variable {E : Type uE} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- A nonnegative measure having polynomial centered ball growth has a uniform
inverse-power tail whenever the decay exponent exceeds the growth exponent.
The proof uses a geometric majorant, not subtraction of divergent potentials. -/
lemma lintegral_norm_rpow_compl_ball_le (μ : Measure E) {C R a s : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R) (ha : 0 ≤ a) (hs : s < a)
    (hball : ∀ r > 0, μ (Metric.ball (0:E) r) ≤ ENNReal.ofReal (C*r^s)) :
    (∫⁻ y in (Metric.ball (0:E) R)ᶜ, ENNReal.ofReal (‖y‖^(-a)) ∂μ) ≤
      ENNReal.ofReal (C*2^s*R^(s-a)/(1-2^(s-a))) := by
  let F : ℕ → E → ℝ≥0∞ := fun k => (Metric.ball (0:E) (R*2^(k+1))).indicator
    (fun _ => ENNReal.ofReal ((R*2^k)^(-a)))
  have hF : ∀ k, Measurable (F k) := fun k => measurable_const.indicator measurableSet_ball
  have hpoint : ∀ y : E, (Metric.ball (0:E) R)ᶜ.indicator
      (fun y => ENNReal.ofReal (‖y‖^(-a))) y ≤ ∑' k, F k y := by
    intro y
    by_cases hy : y ∈ (Metric.ball (0:E) R)ᶜ
    · have hny : R ≤ ‖y‖ := by simpa only [mem_compl_iff,Metric.mem_ball,dist_zero_right,not_lt] using hy
      obtain ⟨k,hk₁,hk₂⟩ := exists_nat_pow_near ((le_div_iff₀ hR).mpr (by simpa using hny))
        (by norm_num : (1:ℝ)<2)
      have hklo : R*2^k ≤ ‖y‖ := by nlinarith [(le_div_iff₀ hR).mp hk₁]
      have hkhi : ‖y‖ < R*2^(k+1) := by nlinarith [(div_lt_iff₀ hR).mp hk₂]
      have hym : y ∈ Metric.ball (0:E) (R*2^(k+1)) := by simpa [Metric.mem_ball,dist_zero_right] using hkhi
      rw [indicator_of_mem hy]
      apply le_trans _ (ENNReal.le_tsum k)
      dsimp only [F]
      rw [indicator_of_mem hym]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) hklo (neg_nonpos.mpr ha))
    · simp only [indicator_of_notMem hy,zero_le]
  have hgeom : 0 ≤ (2:ℝ)^(s-a) := Real.rpow_nonneg (by norm_num) _
  have hgeomlt : (2:ℝ)^(s-a) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hs)
  have hsumm : Summable (fun k : ℕ => (C*2^s*R^(s-a))*((2:ℝ)^(s-a))^k) :=
    (summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hgeom])).mul_left _
  calc
    _ = ∫⁻ y, (Metric.ball (0:E) R)ᶜ.indicator (fun y => ENNReal.ofReal (‖y‖^(-a))) y ∂μ :=
      (lintegral_indicator measurableSet_ball.compl _).symm
    _ ≤ ∫⁻ y, ∑' k, F k y ∂μ := lintegral_mono hpoint
    _ = ∑' k, ∫⁻ y, F k y ∂μ := lintegral_tsum (fun k => (hF k).aemeasurable)
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((R*2^k)^(-a)) * ENNReal.ofReal (C*(R*2^(k+1))^s) := by
      apply ENNReal.tsum_le_tsum; intro k
      dsimp only [F]
      rw [lintegral_indicator measurableSet_ball,setLIntegral_const]
      gcongr
      exact hball _ (by positivity)
    _ = ∑' k : ℕ, ENNReal.ofReal ((C*2^s*R^(s-a))*((2:ℝ)^(s-a))^k) := by
      apply tsum_congr; intro k
      rw [← ENNReal.ofReal_mul (by positivity),dyadic_power_identity hR]
    _ = ENNReal.ofReal (∑' k : ℕ, (C*2^s*R^(s-a))*((2:ℝ)^(s-a))^k) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm).symm
    _ = _ := by
      rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hgeom]),div_eq_mul_inv]

end HenonLaneEmden.UniformTail
end Tails

end OAI

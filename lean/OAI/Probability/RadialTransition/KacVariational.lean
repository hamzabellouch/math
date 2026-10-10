import OAI.Probability.RadialTransition.UniformConstants

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_kac_variational_grid {q : ℕ} (hq : 0 < q)
    {t β h R₀ a R κ D F C : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
    (hκ : 0 < κ) (hc : κ ≤ β*(t^2/3456)-β*t*a*(1+kernelUpperError q R)/2)
    (hD : 1 ≤ D) (hcut : t*h+β*(t^2/2)+t+1 ≤ κ*D)
    (hDF : D ≤ F) (hF : Real.exp (β*(t^2/2)+t*(h+β*a*D)+1) ≤ F)
    (hC : ∀ v ∈ Icc (0:ℝ) D, boxPressureConstant t β (h+β*a*v) (∑' n, b n) ≤ C) :
    |grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h-
      idealAttraction (grandPressure (familyPotential t b S) t) a β h| ≤
      2*C*R₀/((q:ℝ)/4)+β*a/2*kernelRowError q R*F^2+
        Real.log ((F+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3) := by
  let φ := familyPotential t b S
  let Q := grandPressure φ t
  let s := (q:ℝ)/4
  have hs1 : 1 ≤ s := hq1
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hR1 : 1 ≤ R := hq1.trans hR
  have hrowb := family_row_mono_mass ht0.le ha hrow
  have hst := stable_family_of_master ht0.le hb hS hs hs (fun _ => le_rfl) hrowb
  have hφ := continuous_familyPotential hb hS hs t
  have hbd := bounded_familyPotential hb hS hs t
  have heta := kernelUpperError_nonneg q hR0
  have hcoerc : 2197*t*bumpIntegral⁻¹*(∑' n, b n)/2 ≤ t^2/16 := by nlinarith [sq_nonneg t]
  have hca : κ/t ≤ β*t/3456-β*a/2 := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith [mul_nonneg (show 0 ≤ β*t*a by positivity) heta]
  have hcuta : h+β*t/2+1/t+1 ≤ κ/t*D := by
    apply (mul_le_mul_iff_left₀ ht0).mp
    have he1 : t*(h+β*t/2+1/t+1) = t*h+β*(t^2/2)+t+1 := by field_simp; ring
    have he2 : t*(κ/t*D) = κ*D := by field_simp
    rw [mul_comm _ t, mul_comm (κ/t*D) t, he1, he2]
    exact hcut
  obtain ⟨u, hu, hactive⟩ := family_ideal_exists_active ht hβ ha hb hS hs hrowb
    (div_pos hκ ht0) hca hD hcuta
  have hfinite := ideal_bddAbove_of_active hactive
  have hnonneg := ideal_nonneg_of_active hactive ((family_pressure_data ht hβ hb hS hs hrowb).2.1 h)
  have hC0 : boxPressureConstant t β h (∑' n, b n) ≤ C := by
    simpa only [mul_zero, add_zero] using hC 0 ⟨le_rfl, by linarith⟩
  have hCpos : 0 ≤ C := (boxPressureConstant_nonneg ht0.le hβ.le (tsum_nonneg hb)).trans hC0
  have hbox (v : ℝ) (hv : v ∈ Icc (0:ℝ) D) :
      |finiteGrandPressure φ t s β (h+β*a*v)-Q β (h+β*a*v)| ≤ C*R₀/s := by
    apply (finiteGrandPressure_family_box_error hq ht hβ hb hS hs hR₀ hrange hrowb).trans
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC v hv) (by linarith)) hs0.le
  have hbound (d : ℝ) (hd : d ∈ Icc (0:ℝ) D) :
      finiteGrandPressure φ t s β (h+β*a*d)-β*a/2*d^2 ≤ idealAttraction Q a β h+C*R₀/s := by
    have hsum := le_csSup hfinite (mem_range_self d)
    have hh := (abs_le.mp (hbox d hd)).2
    change attractionBranch Q a d β h ≤ idealAttraction Q a β h at hsum
    dsimp only [attractionBranch] at hsum
    linarith
  have hquad := quadratic_sum_pressure_bound hφ hbd hst ht0 hs1 hβ.le ha heta hκ hc hD
    (show t*h+β*(t^2/2)+2 ≤ κ*D by linarith)
    (fun n x hx => family_density_stability ht0.le hs1 hb hS hs hcoerc x hx)
    (show 0 ≤ idealAttraction Q a β h+C*R₀/s by positivity) hbound
  have hks : Summable (kacSeries φ q R t a β h) := by
    simpa only [kacSeries, φ, s, ← mul_assoc] using hquad.1
  have hup := family_kac_upper_limit hq ht hβ ha hR hq1 hb hS hs hR₀ hrange hrow hks
    (show Real.log (∑' n, kacSeries φ q R t a β h n)/(t*s^3) ≤
      idealAttraction Q a β h+C*R₀/s+β*a*kernelUpperError q R/2*D^2+
        Real.log ((D+2)*s^3)/(t*s^3) by
      simpa only [kacSeries, φ, s, ← mul_assoc] using hquad.2)
  have hFu : Real.exp (β*(t^2/2)+t*(h+β*a*u)+1) ≤ F := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hF
    gcongr
    exact hu.2
  have hlo := family_kac_lower_limit hq ht hβ ha hR hq1 hb hS hs hR₀ hrange hrow hks hFu
  have hboxu := (abs_le.mp (hbox u hu)).1
  have heq := idealAttraction_eq_of_active hactive
  change idealAttraction Q a β h = Q β (h+β*a*u)-β*a/2*u^2 at heq
  have hdel : boxPressureConstant t β h (∑' n, b n)*R₀/s ≤ C*R₀/s :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC0 (by linarith)) hs0.le
  have hDF0 : 0 ≤ D := by linarith
  have hF0 : 0 ≤ F := hDF0.trans hDF
  have herr : β*a*kernelUpperError q R/2*D^2 ≤ β*a/2*kernelRowError q R*F^2 := by
    have hh := mul_le_mul (kernelUpperError_le_row hR0) ((sq_le_sq₀ hDF0 hF0).mpr hDF)
      (sq_nonneg D) (kernelRowError_nonneg q hR0)
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ β*a/2 by positivity)]
  have hlog : Real.log ((D+2)*s^3)/(t*s^3) ≤ Real.log ((F+2)*s^3)/(t*s^3) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  apply abs_le.mpr
  dsimp only [φ, Q, s] at hboxu hdel heq herr hlog hup hlo ⊢
  rw [show 2*C*R₀/((q:ℝ)/4) = 2*(C*R₀/((q:ℝ)/4)) by ring]
  constructor <;> linarith only [hboxu, hdel, heq, herr, hlog, hup, hlo]

end RadialTransition
end

end OAI

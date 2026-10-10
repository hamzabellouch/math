import OAI.Probability.RadialTransition.CoreLocalLower

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def bareAlpha (h : ℝ) : ℝ := max 0 (max h (4*h-9))
def bareLimit (h : ℝ) : ℝ := max 0 (max (packingDensity*h) (packingDensity*(4*h-9)))

lemma bareLimit_eq (h : ℝ) : bareLimit h = bareAlpha h*packingDensity := by
  have hp := packingDensity_pos.le
  simp only [bareLimit, bareAlpha, max_mul_of_nonneg _ _ hp, zero_mul]
  congr 2 <;> ring

lemma packing_coefficient_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ℝ, 0 < ν ∧ ν ≤ 1 ∧ |packingDensity/(1+ν)^3-packingDensity| < ε := by
  have hh : Tendsto (fun x : ℝ => packingDensity/(1+x⁻¹)^3) atTop (nhds packingDensity) := by
    have hh : Tendsto (fun x : ℝ => (1+x⁻¹)^3) atTop (nhds (1:ℝ)) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).add tendsto_inv_atTop_zero).pow 3
    simpa [div_eq_mul_inv] using (hh.inv₀ (by norm_num : (1:ℝ) ≠ 0)).const_mul packingDensity
  have he := (Metric.tendsto_atTop.mp hh ε hε)
  obtain ⟨x, hx⟩ := he
  let y := max x 1
  have hy : 1 ≤ y := le_max_right _ _
  refine ⟨y⁻¹, inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ hy, ?_⟩
  simpa only [Real.dist_eq] using hx y (le_max_left _ _)

lemma tendsto_core_micro : Tendsto microLength atTop (nhds 0) := by
  exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

lemma corePressure_lower_branch {ν b t β h : ℝ} (ht : 1 ≤ t) (hb : 0 < b)
    (hν : 0 ≤ ν) (hsep : 1/t+4*b ≤ ν) (hβ : 0 ≤ β)
    (htb : 3*microLength t ≤ b/2) :
    packingDensity/(1+ν)^3*h-packingDensity*|Real.log (b^3)|/t ≤
      grandPressure (corePotential t) t β h ∧
    packingDensity/(1+ν)^3*(4*h-9)-packingDensity*|Real.log (blobTetraConstant b)|/t ≤
      grandPressure (corePotential t) t β h := by
  let c := packingDensity/(1+ν)^3
  have hp := packingDensity_pos
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hcp : c ≤ packingDensity := by
    dsimp [c]
    exact div_le_self packingDensity_pos.le (one_le_pow₀ (by linarith))
  have ht0 : 0 < t := by linarith
  have hl := corePressure_packing_lower ht hb.le hν hsep hβ (h := h)
  have hh (z : ℝ) : -packingDensity*|z|/t ≤ c*(z/t) := by
    have hz := neg_abs_le z
    have h1 := mul_le_mul_of_nonneg_left hz hc0
    have h2 := mul_le_mul_of_nonneg_right hcp (abs_nonneg z)
    have h3 : -packingDensity*|z| ≤ c*z := by nlinarith
    have h4 := div_le_div_of_nonneg_right h3 ht0.le
    simpa only [mul_div_assoc] using h4
  constructor
  · have hm := mul_le_mul_of_nonneg_left (core_local_log_monomer ht0 hb hβ (h := h)) hc0
    have he := hh (Real.log (b^3))
    dsimp only [c] at hm he
    rw [mul_add] at hm
    simp only [neg_mul, neg_div] at he
    linarith
  · have hm := mul_le_mul_of_nonneg_left (core_local_log_tetra ht0 hb hβ htb (h := h)) hc0
    have he := hh (Real.log (blobTetraConstant b))
    dsimp only [c] at hm he
    rw [mul_add] at hm
    simp only [neg_mul, neg_div] at he
    linarith

lemma corePressure_uniform_bare {β₀ H ε : ℝ} (hβ₀ : 0 < β₀) (hH : 0 ≤ H) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ β h : ℝ, β₀ ≤ β → |h| ≤ H →
      |grandPressure (corePotential t) t β h-bareLimit h| ≤ ε := by
  let D : ℝ := 4*H+10
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨ν, hν, _, hc⟩ := packing_coefficient_approx (div_pos hε (mul_pos (by norm_num : (0:ℝ)<2) hD))
  let b := ν/10
  let c := packingDensity/(1+ν)^3
  let K := packingDensity*(|Real.log (b^3)|+|Real.log (blobTetraConstant b)|)
  have hb : 0 < b := by dsimp [b]; positivity
  have hp := packingDensity_pos
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlim1 : Tendsto (fun t : ℝ => 1/t) atTop (nhds 0) := by simpa using tendsto_inv_atTop_zero
  have hsep : ∀ᶠ t : ℝ in atTop, 1/t+4*b ≤ ν := by
    have hh := ((hlim1.add_const (4*b)).eventually (eventually_le_nhds (by dsimp [b]; linarith : 0+4*b < ν)))
    exact hh
  have hmic : ∀ᶠ t : ℝ in atTop, 3*microLength t ≤ b/2 :=
    (tendsto_core_micro.const_mul 3).eventually (eventually_le_nhds (by linarith : (3:ℝ)*0 < b/2))
  have hsmall : ∀ᶠ t : ℝ in atTop, 2*((1+(1:ℝ)/1000)*microLength t) < 1 := by
    have hh := (tendsto_core_micro.const_mul (2*(1+(1:ℝ)/1000))).eventually
      (eventually_lt_nhds (by norm_num : 2*(1+(1:ℝ)/1000)*0 < 1))
    simpa only [mul_assoc] using hh
  have herror : ∀ᶠ t : ℝ in atTop, K/t ≤ ε/2 := by
    have hh : Tendsto (fun t : ℝ => K/t) atTop (nhds 0) := by simpa [div_eq_mul_inv] using hlim1.const_mul K
    exact hh.eventually (eventually_le_nhds (by positivity : (0:ℝ)<ε/2))
  have hupper : ∀ᶠ t : ℝ in atTop, (216*Real.log 15001+1)/t ≤ ε := by
    have hh : Tendsto (fun t : ℝ => (216*Real.log 15001+1)/t) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hlim1.const_mul (216*Real.log 15001+1)
    exact hh.eventually (eventually_le_nhds hε)
  filter_upwards [eventually_ge_atTop (max 1 (2*H/β₀)), hsep, hmic, hsmall, herror, hupper]
    with t ht hsep hmic hsmall herror hupper
  intro β h hβ hh
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hβpos : 0 < β := hβ₀.trans_le hβ
  have hhH := abs_le.mp hh
  have hα0 : 0 ≤ bareAlpha h := le_max_left _ _
  have hα1 : h ≤ bareAlpha h := (le_max_left _ _).trans (le_max_right _ _)
  have hα4 : 4*h-9 ≤ bareAlpha h := (le_max_right _ _).trans (le_max_right _ _)
  have hup := corePressure_upper ht1 hsmall hβpos.le hα0 hα1 hα4
  have hexp : Real.exp (t*h-β*t^2/2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hth : 2*H ≤ t*β₀ := (div_le_iff₀ hβ₀).mp ((le_max_right _ _).trans ht)
    have hh1 := mul_le_mul_of_nonneg_right hth ht0.le
    have hh2 := mul_le_mul_of_nonneg_right hβ (sq_nonneg t)
    have hh3 := mul_le_mul_of_nonneg_left hhH.2 ht0.le
    nlinarith
  have hup' : grandPressure (corePotential t) t β h-bareLimit h ≤ ε := by
    rw [bareLimit_eq]
    have hdiv := div_le_div_of_nonneg_right (show 216*Real.log 15001+Real.exp (t*h-β*t^2/2) ≤ 216*Real.log 15001+1 by linarith) ht0.le
    linarith
  have hlo := corePressure_lower_branch ht1 hb hν.le hsep hβpos.le hmic (h := h)
  have hz := (grandPressure_spec (continuous_corePotential t) (bounded_corePotential t)
    (stable_corePotential t) ht0 hβpos.le (core_nonpos_outer ht1) h).2.1
  have hcoeff (x : ℝ) (hx : |x| ≤ D) : |packingDensity*x-c*x| ≤ ε/2 := by
    have he : packingDensity*x-c*x = (packingDensity-c)*x := by ring
    rw [he, abs_mul]
    have hcx : |packingDensity-c| ≤ ε/(2*D) := by
      dsimp [c]
      rw [abs_sub_comm]
      exact hc.le
    calc
      _ ≤ (ε/(2*D))*D := mul_le_mul hcx hx (abs_nonneg _) (by positivity)
      _ = ε/2 := by field_simp
  have he1 := hcoeff h (hh.trans (by dsimp [D]; linarith))
  have he4 := hcoeff (4*h-9) (by rw [abs_le]; dsimp [D]; constructor <;> linarith)
  have hlog1 : packingDensity*|Real.log (b^3)|/t ≤ ε/2 := by
    apply le_trans _ herror
    apply div_le_div_of_nonneg_right _ ht0.le
    dsimp [K]
    nlinarith [packingDensity_pos, abs_nonneg (Real.log (blobTetraConstant b))]
  have hlog4 : packingDensity*|Real.log (blobTetraConstant b)|/t ≤ ε/2 := by
    apply le_trans _ herror
    apply div_le_div_of_nonneg_right _ ht0.le
    dsimp [K]
    nlinarith [packingDensity_pos, abs_nonneg (Real.log (b^3))]
  have hlo' : bareLimit h-grandPressure (corePotential t) t β h ≤ ε := by
    have h1 : packingDensity*h ≤ grandPressure (corePotential t) t β h+ε := by
      have hh := (abs_le.mp he1).2
      dsimp only [c] at hh
      linarith [hlo.1]
    have h4 : packingDensity*(4*h-9) ≤ grandPressure (corePotential t) t β h+ε := by
      have hh := (abs_le.mp he4).2
      dsimp only [c] at hh
      linarith [hlo.2]
    have hm : bareLimit h ≤ grandPressure (corePotential t) t β h+ε :=
      max_le (by linarith) (max_le h1 h4)
    linarith
  exact abs_le.mpr ⟨by linarith, hup'⟩

end RadialTransition
end

end OAI

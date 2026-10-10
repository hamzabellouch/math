import OAI.Analysis.LiebThirring.IntervalAction

namespace OAI


noncomputable section
namespace SharpLiebThirring.ConstantProof
open MeasureTheory Set Filter
open scoped Topology

def betaAction (σ : ℝ) : ℝ := ∫ t in (-1 : ℝ)..1, (1-t^2)^σ

lemma real_beta_symmetric {σ : ℝ} (hσ : 0 < σ) :
    (∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ) =
      Real.Gamma (σ+1)^2 / Real.Gamma (2*(σ+1)) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div ((σ+1 : ℝ) : ℂ) ((σ+1 : ℝ) : ℂ)
    (by simpa using (show 0 < σ+1 by linarith)) (by simpa using (show 0 < σ+1 by linarith))
  have hi : Complex.betaIntegral ((σ+1 : ℝ) : ℂ) ((σ+1 : ℝ) : ℂ) =
      ((∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ : ℝ) : ℂ) := by
    rw [Complex.betaIntegral,← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    push_cast
    rw [add_sub_cancel_right,← Complex.ofReal_cpow hx.1,
      show (1 : ℂ)-(x : ℂ) = ((1-x : ℝ) : ℂ) by push_cast; rfl,← Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
  rw [hi,Complex.Gamma_ofReal,← Complex.ofReal_add,
    Complex.Gamma_ofReal] at h
  have hh : (σ+1)+(σ+1) = 2*(σ+1) := by ring
  rw [hh] at h
  have hh' : (∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ) =
      Real.Gamma (σ+1)*Real.Gamma (σ+1) / Real.Gamma (2*(σ+1)) := by exact_mod_cast h
  simpa only [pow_two] using hh'

lemma betaAction_eq_beta {σ : ℝ} (_hσ : 0 < σ) :
    betaAction σ = 2 * (4 : ℝ)^σ * (∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ) := by
  have h := intervalIntegral.integral_comp_mul_add
    (fun x : ℝ ↦ (1-x^2)^σ) (a := 0) (b := 1) (c := (2 : ℝ)) (by norm_num) (-1)
  norm_num at h
  have hi : (∫ t in (0 : ℝ)..1, (1-(2*t-1)^2)^σ) =
      (4 : ℝ)^σ * (∫ t in (0 : ℝ)..1, t^σ*(1-t)^σ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    dsimp only
    rw [show 1-(2*x-1)^2 = 4*(x*(1-x)) by ring,
      Real.mul_rpow (by norm_num) (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)),
      Real.mul_rpow hx.1 (sub_nonneg.mpr hx.2)]
  rw [show (fun x : ℝ ↦ (1-(2*x+ -1)^2)^σ) = fun x ↦ (1-(2*x-1)^2)^σ by ext; congr 2] at h
  rw [hi] at h
  unfold betaAction
  linarith

lemma betaAction_pos {σ : ℝ} (hσ : 0 < σ) : 0 < betaAction σ := by
  rw [betaAction_eq_beta hσ,real_beta_symmetric hσ]
  have hG := Real.Gamma_pos_of_pos (show 0 < σ+1 by linarith)
  have hG' := Real.Gamma_pos_of_pos (show 0 < 2*(σ+1) by linarith)
  positivity

end SharpLiebThirring.ConstantProof
namespace SharpLiebThirring.ConstantProof
open MeasureTheory Set Filter
open scoped Topology

lemma betaAction_eq_Gamma {σ : ℝ} (hσ : 0 < σ) :
    betaAction σ = Real.sqrt Real.pi * Real.Gamma (σ+1) / Real.Gamma (σ+3/2) := by
  have h := Real.Gamma_mul_Gamma_add_half (σ+1)
  have he : σ+1+1/2 = σ+3/2 := by ring
  rw [he] at h
  have hp : (2 : ℝ)*4^σ*2^(1-2*(σ+1)) = 1 := by
    have hh : (2 : ℝ)*4^σ*2^(1-2*(σ+1)) = 2^(1+2*σ+(1-2*(σ+1))) := by
      rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num),Real.rpow_one,
        Real.rpow_mul (by norm_num),Real.rpow_two]
      norm_num
    rw [hh,show 1+2*σ+(1-2*(σ+1)) = 0 by ring,Real.rpow_zero]
  have hg' : Real.Gamma (σ+3/2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < σ+3/2)).ne'
  have hg'' : Real.Gamma (2*(σ+1)) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity : 0 < 2*(σ+1))).ne'
  rw [betaAction_eq_beta hσ,real_beta_symmetric hσ]
  apply (eq_div_iff hg').mpr
  calc
    (2*4^σ*(Real.Gamma (σ+1)^2/Real.Gamma (2*(σ+1))))*Real.Gamma (σ+3/2) =
        (Real.Gamma (σ+1)/Real.Gamma (2*(σ+1)))*(2*4^σ*(Real.Gamma (σ+1)*Real.Gamma (σ+3/2))) := by ring
    _ = (Real.Gamma (σ+1)/Real.Gamma (2*(σ+1)))*(2*4^σ*(Real.Gamma (2*(σ+1))*2^(1-2*(σ+1))*Real.sqrt Real.pi)) := by rw [h]
    _ = (Real.Gamma (σ+1)/Real.Gamma (2*(σ+1)))*(Real.Gamma (2*(σ+1))*Real.sqrt Real.pi) := by
      congr 1
      calc
        _ = Real.Gamma (2*(σ+1))*Real.sqrt Real.pi*(2*4^σ*2^(1-2*(σ+1))) := by ring
        _ = _ := by rw [hp,mul_one]
    _ = _ := by field_simp

lemma boundary_action_scaling {σ k : ℝ} (_hσ : 0 < σ) (hk : 0 < k) :
    (∫ s in -k..k, (k^2-s^2)^σ) = k^(1+2*σ)*betaAction σ := by
  have hi := intervalIntegral.integral_comp_mul_left (fun s : ℝ ↦ (k^2-s^2)^σ)
    (a := -1) (b := 1) (c := k) hk.ne'
  simp only [mul_neg_one,mul_one] at hi
  have hj : (∫ s in (-1 : ℝ)..1, (k^2-(k*s)^2)^σ) = k^(2*σ)*betaAction σ := by
    rw [betaAction,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    dsimp only
    have hs' : 0 ≤ 1-s^2 := by nlinarith [hs.1,hs.2]
    rw [show k^2-(k*s)^2 = k^2*(1-s^2) by ring,Real.mul_rpow (sq_nonneg _) hs',
      ← Real.rpow_two k,← Real.rpow_mul hk.le]
  rw [hj] at hi
  have he : k^(1+2*σ) = k*k^(2*σ) := by rw [Real.rpow_add hk,Real.rpow_one]
  rw [he]
  simp only [smul_eq_mul] at hi
  field_simp [hk.ne'] at hi
  nlinarith [hi]

lemma young_over_beta {σ : ℝ} (hσ : 0 < σ) :
    (σ^σ/(1+σ)^(1+σ))/betaAction σ =
      (σ/(σ+1))^σ*Real.Gamma (σ+3/2)/(Real.sqrt Real.pi*Real.Gamma (σ+2)) := by
  have hg := Real.Gamma_add_one (show σ+1 ≠ 0 by linarith)
  rw [show σ+1+1 = σ+2 by ring] at hg
  rw [betaAction_eq_Gamma hσ,Real.div_rpow hσ.le (by linarith : 0 ≤ σ+1),
    show 1+σ = σ+1 by ring,Real.rpow_add (by linarith : 0 < σ+1),Real.rpow_one,hg]
  field_simp

end SharpLiebThirring.ConstantProof

end

end OAI

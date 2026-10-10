import OAI.NumberTheory.DirichletL.Detector.RadialMellin
import OAI.NumberTheory.DirichletL.Detector.HighAbsolute
import OAI.NumberTheory.DirichletL.Detector.FrequencySupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma radialFourier_vertical_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ r : ℝ) (hσ : 0<σ) (hr : 0<r) :
    paperRadialFourier W r=verticalIntegral σ (fun z=>(r:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  have he := ProbeRadialMellin.radial_mellin_inversion W a b ha hW σ r hσ hr
  simpa only [mellinInv,verticalIntegral,Complex.real_smul,smul_eq_mul] using he.symm

lemma radial_sum_exchange {ι : Type*} [Countable ι] (W : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W⊆Set.Icc a b)
    (σ : ℝ) (hσ : 0<σ) (c : ι→ℂ) (r : ι→ℝ) (hr : ∀i,0<r i)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    (∑'i,c i*paperRadialFourier W (r i))=
      verticalIntegral σ (fun z=>∑'i,c i*(r i:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  let F := fun i (t : ℝ)=>c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*
    mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)
  have hF (i) : Integrable (F i) := by
    simpa only [F,mul_assoc] using
      (ProbeRadialMellin.radial_mellin_inverse_integrable W a b ha hW σ (r i) hσ (hr i)).const_mul (c i)
  have hn (i) (t : ℝ) : ‖F i t‖=(‖c i‖*(r i)^(-σ))*
      ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hr i)]
    simp
  have hsum : Summable (fun i=>∫t : ℝ,‖F i t‖) := by
    simp only [hn,integral_const_mul]
    exact hc.mul_right _
  have he := integral_tsum_of_summable_integral_norm hF hsum
  simp_rw [radialFourier_vertical_inverse W a b ha hW σ _ hσ (hr _)]
  unfold verticalIntegral
  have hi (i) : c i*(↑(1/(2*Real.pi))*(∫t : ℝ,
      (r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)))=
      (↑(1/(2*Real.pi)):ℂ)*(∫t : ℝ,F i t) := by
    simp only [F,mul_assoc,integral_const_mul]
    ring
  simp_rw [hi]
  rw [tsum_mul_left,he]

lemma frequency_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>(elementNorm H.val)^(-σ)) := by
  have he (H : NonzeroFrequency) : ‖frequencyWeight (σ:ℂ) H‖=(elementNorm H.val)^(-σ) := by
    have hH : 0<elementNorm H.val := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr H.property))
    rw [frequencyWeight,Complex.norm_cpow_eq_rpow_re_of_pos hH]
    simp
  simpa only [he,Complex.ofReal_re] using frequencyWeight_summable_norm (σ:ℂ) hσ

theorem actualFrequency_moment_summable (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>‖actualCongruenceCoefficient C A s hA H.val‖*
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)) := by
  have hd : 0<elementNorm ((C.generator*A)*s) := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
  have hr (H : NonzeroFrequency) :
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)=
        (K/elementNorm ((C.generator*A)*s))^(-σ)*(elementNorm H.val)^(-σ) := by
    rw [show K*elementNorm H.val/elementNorm ((C.generator*A)*s)=
      (K/elementNorm ((C.generator*A)*s))*elementNorm H.val by ring]
    apply Real.mul_rpow (div_pos hK hd).le
    unfold elementNorm
    positivity
  simp only [hr]
  have hb := (frequency_rpow_summable σ hσ).mul_left
    (((Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {C.generator*A}):ℝ))*
      (K/elementNorm ((C.generator*A)*s))^(-σ))
  apply Summable.of_nonneg_of_le (fun H=>mul_nonneg (norm_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (div_pos hK hd).le _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _))) _ hb
  intro H
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (actualCongruenceCoefficient_norm_le C A s hA hs H.val)
      (Real.rpow_nonneg (div_pos hK hd).le _)) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)

end SevenEighths.ProbePhysical
end

end OAI

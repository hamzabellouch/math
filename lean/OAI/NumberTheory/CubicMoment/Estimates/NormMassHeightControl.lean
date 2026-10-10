import OAI.NumberTheory.CubicMoment.Estimates.UniformNormHeight

namespace OAI

/-! The signed norm-Mellin bound with an explicit, profile-independent
mass budget. The change of variables retains its exact Jacobian. -/
noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform
namespace CubicFirstMoment

lemma dyadicHeightMean_scaled_convolution_uniform {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hf0 : ∀ s, 0 ≤ f s)
    (hG : Continuous G) {M B T c : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M)
    (hT : 0 < T) (hc : 0 < c)
    (hmean : ∀ v, dyadicHeightMean (fun t => G (t+v)) T ≤ B) (u : ℝ) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+c*s)) T ≤ B*(∫ s : ℝ, f s) := by
  let w := fun s : ℝ => c⁻¹*f (s/c)
  have hw : Continuous w := continuous_const.mul (hf.comp (continuous_id.div_const c))
  have hwi : Integrable w := (hfi.comp_div hc.ne').const_mul _
  have hw0 : ∀ s, 0 ≤ w s := fun s => mul_nonneg (inv_nonneg.mpr hc.le) (hf0 _)
  have hi : (∫ s : ℝ, w s) = ∫ s : ℝ, f s := by
    dsimp [w]
    rw [integral_const_mul,Measure.integral_comp_div f c,abs_of_pos hc,smul_eq_mul]
    field_simp
  have he (t : ℝ) : (∫ s : ℝ, f s*G (t+u+c*s)) = ∫ s : ℝ, w s*G (t+u+s) := by
    rw [integral_scaled_mass f (fun s => G (t+u+s)) hc]
    simp only [w,integral_const_mul,mul_assoc]
  simp_rw [he]
  exact (dyadicHeightMean_convolution_uniform hw hwi hw0 hG hbound hT hmean u).trans_eq
    (by rw [hi])

theorem normMellin_signed_height_of_mass (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) (D : ℝ)
    (hmass : ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ s : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖) ≤ D)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (G : ℝ → ℝ) (hG : Continuous G) (E B T u : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hbound : ∀ t, ‖G t‖ ≤ E)
    (hmean : ∀ v, dyadicHeightMean (fun t => G (t+v)) T ≤ B) :
    (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
      ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
        ((G (t+u+2*Real.pi*s)+G (t+u-(2*Real.pi*s)))/2)) T ≤ D*B := by
  let f := fun s : ℝ => ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖
  have hf : Continuous f := (𝓕 (normDenominatorLogSchwartz M hM V hV hV' ρ)).continuous.norm
  have hfi : Integrable f := (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
  have hp := dyadicHeightMean_scaled_convolution_uniform hf hfi (fun _ => _root_.norm_nonneg _)
    hG hbound hT (by positivity : 0 < 2*Real.pi) hmean u
  have hn := dyadicHeightMean_scaled_convolution_uniform (hf.comp continuous_neg) hfi.comp_neg
    (fun _ => _root_.norm_nonneg _) hG hbound hT (by positivity : 0 < 2*Real.pi) hmean u
  have he (t : ℝ) : (∫ s : ℝ, f s*G (t+u-(2*Real.pi*s))) =
      ∫ s : ℝ, f (-s)*G (t+u+2*Real.pi*s) := by
    have he := integral_neg_eq_self (fun s : ℝ => f s*G (t+u-(2*Real.pi*s))) volume
    simpa only [mul_neg,sub_neg_eq_add] using he.symm
  have hfc : Continuous (fun t => ∫ s : ℝ, f s*G (t+u+2*Real.pi*s)) := by
    have he (t : ℝ) := integral_scaled_mass f (fun s => G (t+u+s)) (by positivity : 0 < 2*Real.pi)
    simp_rw [he]
    exact continuous_const.mul (continuous_height_convolution
      (hf.comp (continuous_id.div_const _)) (hfi.comp_div (by positivity : 2*Real.pi ≠ 0))
      hG hbound u)
  have hnc : Continuous (fun t => ∫ s : ℝ, f s*G (t+u-(2*Real.pi*s))) := by
    simp_rw [he]
    have he' (t : ℝ) := integral_scaled_mass (fun s => f (-s)) (fun s => G (t+u+s))
      (by positivity : 0 < 2*Real.pi)
    simp_rw [he']
    exact continuous_const.mul (continuous_height_convolution
      ((hf.comp continuous_neg).comp (continuous_id.div_const _))
      (hfi.comp_neg.comp_div (by positivity : 2*Real.pi ≠ 0)) hG hbound u)
  have hi (t : ℝ) : (∫ s : ℝ, f s*((G (t+u+2*Real.pi*s)+G (t+u-(2*Real.pi*s)))/2)) =
      ((∫ s : ℝ, f s*G (t+u+2*Real.pi*s))+
       (∫ s : ℝ, f s*G (t+u-(2*Real.pi*s))))/2 := by
    have hip : Integrable (fun s : ℝ => f s*G (t+u+2*Real.pi*s)) :=
      hfi.mul_bdd (hG.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => hbound _))
    have hin : Integrable (fun s : ℝ => f s*G (t+u-(2*Real.pi*s))) :=
      hfi.mul_bdd (hG.comp (continuous_const.sub (continuous_const.mul continuous_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => hbound _))
    simp_rw [←mul_div_assoc,mul_add]
    rw [integral_div,integral_add hip hin]
  have hn' : dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u-(2*Real.pi*s))) T ≤
      B*(∫ s : ℝ, f s) := by
    simp_rw [he]
    exact hn.trans_eq (by simp only [Function.comp_apply]; rw [integral_neg_eq_self])
  change (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
    f s*((G (t+u+2*Real.pi*s)+G (t+u-(2*Real.pi*s)))/2)) T ≤ _
  simp_rw [hi]
  simp_rw [div_eq_mul_inv, mul_comm _ (2:ℝ)⁻¹]
  rw [dyadicHeightMean_const_mul,dyadicHeightMean_add hfc hnc]
  have hb := add_le_add hp hn'
  have hd := mul_le_mul_of_nonneg_left (hmass ρ hρ) hB
  nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ (1+ρ)^q by positivity)]

end CubicFirstMoment

end

end OAI

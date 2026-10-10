import OAI.NumberTheory.DirichletL.Detector.LowCutoff
import OAI.NumberTheory.DirichletL.Detector.PhysicalNorms

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical

lemma low_mellin_phase_norm (a v : ℝ) (ha : 0<a) :
    ‖(a:ℂ)^((v:ℂ)*Complex.I)‖=1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
  simp

lemma low_mellin_ratio_integrable (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Integrable (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*
      mellin W ((v:ℂ)*Complex.I)) := by
  have hm : Integrable (fun v : ℝ=>mellin W ((v:ℂ)*Complex.I)) := by
    have hh := compactMellin_vertical_integrable W a0 b0 ha0 hW hWs 0
    change Integrable (fun v : ℝ=>mellin W ((0:ℂ)+v*Complex.I)) at hh
    simpa using hh
  have hc : Continuous (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne')))
  have hp : ∀v : ℝ,‖(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)‖≤1 := by
    intro v
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ha,Complex.norm_cpow_eq_rpow_re_of_pos hb]
    simp
  simpa only [mul_comm] using hm.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hp)

lemma low_mellin_ratio (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    W (a/b)=(1/(2*Real.pi):ℂ)*∫v : ℝ,
      (a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  rw [compactMellin_inversion W a0 b0 ha0 hW hWs 0 _ (div_pos ha hb)]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  rw [Complex.ofReal_zero,zero_add,Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg ha.le hb.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg,neg_neg]

lemma low_sqrt_ratio (B q X Y : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) :
    (Real.sqrt (B*q*X):ℂ)⁻¹=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*((q/Y:ℝ):ℂ)^(-(1/2:ℂ)) := by
  have hQ : 0<B*X*Y := by positivity
  have hb : 0<q/Y := div_pos hq hY
  have he : B*q*X=(B*X*Y)*(q/Y) := by field_simp
  rw [he,Real.sqrt_mul hQ.le,Complex.ofReal_mul,Complex.cpow_neg,ProbeEuler.cpow_half_eq_sqrt _ hb.le]
  simp only [mul_inv_rev,mul_comm]

theorem physical_radial_low_mellin (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (B q X Y m : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hm : 0<m) :
    (Real.sqrt (B*q*X):ℂ)⁻¹*W (m/(B*q*X))=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  have hQ : 0<B*X*Y := by positivity
  have ha : 0<m/(B*X*Y) := div_pos hm hQ
  have hb : 0<q/Y := div_pos hq hY
  have hbc : ((q/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have he : m/(B*q*X)=(m/(B*X*Y))/(q/Y) := by field_simp
  rw [he,low_mellin_ratio W a0 b0 ha0 hW hWs _ _ ha hb,low_sqrt_ratio B q X Y hB hq hX hY]
  simp_rw [Complex.cpow_add _ _ hbc]
  rw [show (fun v : ℝ=>((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
    (((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I))*mellin W ((v:ℂ)*Complex.I))=
    (fun v : ℝ=>((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*
      (((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I))) by funext v; ring]
  rw [integral_const_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

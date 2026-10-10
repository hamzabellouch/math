import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCutoffMeasurable
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCoordinateEnergy

namespace OAI

/-! The actual cutoff radial derivative is integrable on each exact
cusp cell. The majorant is the already proved global mass plus energy. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaHorizontalCell_measurable : MeasurableSet cubicThetaHorizontalCell := by
  have hm (i : Fin 2) : Measurable (fun z => cubicThetaPeriodCoordinates z i) :=
    ((continuous_apply i).comp cubicThetaPeriodCoordinates_continuous).measurable
  convert MeasurableSet.iInter (fun i =>
    (measurableSet_Ico : MeasurableSet (Ico (0:ℝ) 1)).preimage (hm i)) using 1
  ext z
  simp only [cubicThetaHorizontalCell,mem_iInter,mem_preimage,mem_ofPred_eq]

lemma cubicThetaCuspCutoff_derivative_majorant :
    ∃ C≥0, ∀ (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) (z : ℂ) (v : ℝ), 0<v →
      ‖deriv (cubicThetaCuspCutoffSection δ F z) v‖^2/v≤
        C*cubicThetaCuspCoordinateEnergy δ F (z,v)/v^3 := by
  classical
  obtain ⟨B,hB,h⟩ := cubicThetaCuspCutoff_energy (by norm_num : (0:ℝ)<1)
  refine ⟨2+B,by positivity,?_⟩
  intro δ F z v hv
  have ht := h δ F z v hv
  norm_num only at ht
  let M := ‖cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex δ) (z,v))‖^2
  let E := cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv)
  have hM : 0≤M := sq_nonneg _
  have hE : 0≤E := cubicThetaSectionEnergy_nonneg F _
  have hi : (Icc (1:ℝ) 2).indicator (fun t => ‖cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))‖^2) v≤M := by
    by_cases hv' : v∈Icc (1:ℝ) 2
    · rw [indicator_of_mem hv']
    · rw [indicator_of_notMem hv']
      exact hM
  have hmul := mul_le_mul_of_nonneg_left hi hB
  have ht' : v^2*‖deriv (cubicThetaCuspCutoffSection δ F z) v‖^2≤(2+B)*(M+E) := by
    change _≤2*E+B*_ at ht
    nlinarith [mul_nonneg hB hE]
  rw [cubicThetaCuspCoordinateEnergy_norm δ F z hv]
  have hd := div_le_div_of_nonneg_right ht' (pow_nonneg hv.le 3)
  convert hd using 1
  field_simp [hv.ne']

lemma cubicThetaCuspCutoff_derivative_integrable_high (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun y : ℂ × ℝ => ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)
      (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)) := by
  obtain ⟨C,_,hC⟩ := cubicThetaCuspCutoff_derivative_majorant
  have he := (cubicThetaCuspCoordinateEnergy_integrable δ F (le_refl 1)).const_mul C
  have hm : IntegrableOn (fun y : ℂ × ℝ => C*cubicThetaCuspCoordinateEnergy δ F y/y.2^3)
      (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)) := by
    simpa only [IntegrableOn,mul_div_assoc] using he
  apply hm.mono'
  · exact (((cubicThetaCuspCutoff_deriv_measurable δ F).norm.pow_const 2).div
      measurable_snd).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
    have hv : 0<y.2 := lt_trans zero_lt_one hy.2
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) hv.le)]
    exact hC δ F y.1 y.2 hv

lemma cubicThetaCuspCutoffSection_deriv_zero (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : v≤1) : deriv (cubicThetaCuspCutoffSection δ F z) v=0 := by
  apply HasDerivWithinAt.deriv_eq_zero _ (uniqueDiffWithinAt_Iic v)
  apply (hasDerivWithinAt_const v (Iic v) (0:ℂ)).congr_of_mem _ (by simp)
  intro w hw
  change cubicThetaCuspCutoff w*_=0
  rw [cubicThetaCuspCutoff_zero (hw.trans hv),zero_mul]

lemma cubicThetaCuspCell_integrable_extend {f : ℂ × ℝ → ℝ}
    (hf : IntegrableOn f (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)))
    (hz : ∀ z v, v≤1 → f (z,v)=0) :
    IntegrableOn f (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)) := by
  classical
  have hi := (integrable_indicator_iff (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)).mpr hf
  have h := hi.integrableOn (s:=cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ))
  apply h.congr
  filter_upwards [ae_restrict_mem (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
  change (cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)).indicator f y=f y
  by_cases hv : 1<y.2
  · exact indicator_of_mem (s:=cubicThetaHorizontalCell ×ˢ Ioi (1:ℝ)) ⟨hy.1,hv⟩ f
  · rw [indicator_of_notMem (by rintro ⟨_,h⟩; exact hv h)]
    exact (hz y.1 y.2 (le_of_not_gt hv)).symm

theorem cubicThetaCuspCutoff_derivative_integrable (δ : SL(2,Eisenstein))
    (F : cubicThetaSmoothTests) :
    IntegrableOn (fun y : ℂ × ℝ => ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)
      (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)) := by
  apply cubicThetaCuspCell_integrable_extend (cubicThetaCuspCutoff_derivative_integrable_high δ F)
  intro z v hv
  rw [cubicThetaCuspCutoffSection_deriv_zero δ F z hv,norm_zero,
    zero_pow (by norm_num : (2:ℕ)≠0),zero_div]

end CubicFirstMoment

end

end OAI

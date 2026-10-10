import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedHorizontalContinuity

namespace OAI

/-! Weighted height identities for the actual translated theta coefficients. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaShiftedModel_window_pairing (b h : Eisenstein) (W : C_c(ℝ,ℂ))
    {a : ℝ} (ha : 0<a) (d : ℝ) :
    (∫ p in cubicThetaShiftedWindow a d,star (cubicThetaShiftedFourierWeight h W p)*
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
        (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p.val)
      ∂cubicThetaPointMeasure)=
    ∫ v in Icc a d,star (W v)*cubicThetaShiftedModelHorizontal b h v/(v:ℂ)^3 := by
  obtain ⟨K,hK,hSK,_⟩ := cubicThetaShiftedWindow_compact_container ha d
  let f : ℂ×ℝ → ℂ := fun p => star (W p.2*
      (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency h)):ℂ))*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaMobius (cubicThetaFullComplex (cubicThetaShiftedInversion b)) p)
  have hi : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaShiftedWindow a d) cubicThetaPointMeasure :=
    cubicThetaShiftedWindowTest_integrable h W a d hK hSK _ _
      (cubicThetaCompactShiftedResidue_model b hK)
  change (∫ p in cubicThetaShiftedWindow a d,f (cubicThetaPointCoordinates p)
    ∂cubicThetaPointMeasure)=_
  rw [cubicThetaShiftedWindow_fubini ha d f hi]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v _
  dsimp only
  rw [cubicThetaShiftedModelHorizontal,←integral_const_mul,←integral_div]
  apply setIntegral_congr_fun cubicThetaShiftedHorizontalCell_measurable
  intro z _
  simp only [f,star_mul]
  ring

def cubicThetaShiftedResidueFactor (n : ℤ) (h : Eisenstein) : ℂ :=
  cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
    cubicThetaRegularizedShiftedFrequency n h (4/3)

lemma cubicThetaShiftedResidue_window_eq (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 1<a) (had : a≤d) :
    (∫ v in Icc a d,star (W v)*cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v/(v:ℂ)^3)=
    ∫ v in Icc a d,star (W v)*
      (cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v)/(v:ℂ)^3 := by
  obtain ⟨K,hK,hSK,hbound⟩ := cubicThetaShiftedWindow_compact_container (by linarith : 0<a) d
  rw [←cubicThetaShiftedModel_window_pairing _ h W (by linarith) d,
    cubicThetaShiftedWindow_residue_coefficient m n hh W (by linarith) had hK hSK
      (fun p hp => ha.trans_le (hbound p hp))]
  rw [cubicThetaShiftedWindowRadialTest,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v _
  unfold cubicThetaShiftedResidueFactor cubicThetaShiftedPoleRadial
  ring

lemma cubicThetaShiftedResidue_window_zero (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 1<a) (had : a≤d) :
    (∫ v in Icc a d,star (W v)*
      ((cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v-
        cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v)/(v:ℂ)^3))=0 := by
  have hpos : ∀ v∈Icc a d,(v:ℂ)^3≠0 := fun v hv =>
    pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by have := hv.1; linarith))
  have hF : ContinuousOn (fun v => star (W v)*
      cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v/(v:ℂ)^3) (Icc a d) :=
    (W.continuous.star.continuousOn.mul
      ((cubicThetaShiftedModelHorizontal_continuous _ h).mono
        (fun _ hv => lt_of_lt_of_le (lt_trans zero_lt_one ha) hv.1))).div
      (Complex.continuous_ofReal.pow 3).continuousOn hpos
  have hG : ContinuousOn (fun v => star (W v)*
      (cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v)/(v:ℂ)^3) (Icc a d) :=
    (W.continuous.star.continuousOn.mul (continuousOn_const.mul
      ((cubicThetaShiftedPoleRadial_continuous hh).mono
        (fun _ hv => lt_of_lt_of_le (lt_trans zero_lt_one ha) hv.1)))).div
      (Complex.continuous_ofReal.pow 3).continuousOn hpos
  have he := cubicThetaShiftedResidue_window_eq m n hh W ha had
  rw [←sub_eq_zero,←integral_sub (hF.integrableOn_compact isCompact_Icc)
    (hG.integrableOn_compact isCompact_Icc)] at he
  convert he using 1
  congr 1
  ext v
  ring

end CubicFirstMoment

end

end OAI

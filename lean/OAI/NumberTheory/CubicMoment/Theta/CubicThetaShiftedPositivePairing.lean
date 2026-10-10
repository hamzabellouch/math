import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedFullResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedResiduePairing

namespace OAI

/-! Full residue pairings on every positive-height compact interval. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaShiftedPositiveResidue_window_eq (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d) :
    (∫ v in Icc a d,star (W v)*cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v/(v:ℂ)^3)=
    ∫ v in Icc a d,star (W v)*
      (cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v)/(v:ℂ)^3 := by
  obtain ⟨K,hK,hSK,_⟩ := cubicThetaShiftedWindow_compact_container (by linarith : 0<a) d
  rw [←cubicThetaShiftedModel_window_pairing _ h W (by linarith) d,
    cubicThetaShiftedFullWindow_residue_coefficient m n hh W (by linarith) had hK hSK]
  rw [cubicThetaShiftedWindowRadialTest,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v _
  unfold cubicThetaShiftedResidueFactor cubicThetaShiftedPoleRadial
  ring

lemma cubicThetaShiftedPositiveResidue_window_zero (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {a d : ℝ} (ha : 0<a) (had : a≤d) :
    (∫ v in Icc a d,star (W v)*
      ((cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v-
        cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v)/(v:ℂ)^3))=0 := by
  have hpos : ∀ v∈Icc a d,(v:ℂ)^3≠0 := fun v hv =>
    pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by have := hv.1; linarith))
  have hF : ContinuousOn (fun v => star (W v)*
      cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v/(v:ℂ)^3) (Icc a d) :=
    (W.continuous.star.continuousOn.mul
      ((cubicThetaShiftedModelHorizontal_continuous _ h).mono
        (fun _ hv => lt_of_lt_of_le ha hv.1))).div
      (Complex.continuous_ofReal.pow 3).continuousOn hpos
  have hG : ContinuousOn (fun v => star (W v)*
      (cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v)/(v:ℂ)^3) (Icc a d) :=
    (W.continuous.star.continuousOn.mul (continuousOn_const.mul
      ((cubicThetaShiftedPoleRadial_continuous hh).mono
        (fun _ hv => lt_of_lt_of_le ha hv.1)))).div
      (Complex.continuous_ofReal.pow 3).continuousOn hpos
  have he := cubicThetaShiftedPositiveResidue_window_eq m n hh W ha had
  rw [←sub_eq_zero,←integral_sub (hF.integrableOn_compact isCompact_Icc)
    (hG.integrableOn_compact isCompact_Icc)] at he
  convert he using 1
  congr 1
  ext v
  ring


end CubicFirstMoment

end

end OAI

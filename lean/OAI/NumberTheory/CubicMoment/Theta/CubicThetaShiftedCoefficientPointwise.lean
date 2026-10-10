import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedResiduePairing
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! Compact height tests determine the translated theta coefficient pointwise. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaShiftedCoefficient_on_window (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    {a d v : ℝ} (ha : 1<a) (hv : v∈Ioo a d) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v := by
  let J : ℝ → ℂ := fun t =>
    (cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h t-
      cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h t)/(t:ℂ)^3
  have hsub : Ioo a d⊆Ioi (0:ℝ) := fun t ht => by change 0<t; linarith [ht.1]
  have hJ : ContinuousOn J (Ioo a d) :=
    (((cubicThetaShiftedModelHorizontal_continuous _ h).mono hsub).sub
      (continuousOn_const.mul ((cubicThetaShiftedPoleRadial_continuous hh).mono hsub))).div
      (Complex.continuous_ofReal.pow 3).continuousOn
      (fun t ht => pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt (hsub ht))))
  have hzero : ∀ᵐ t ∂(volume : Measure ℝ),t∈Ioo a d → J t=0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hJ.locallyIntegrableOn measurableSet_Ioo)
    intro g hg hgc hgs
    let W : C_c(ℝ,ℂ) :=
      ⟨⟨fun t => (g t:ℂ),Complex.continuous_ofReal.comp hg.continuous⟩,
        hgc.comp_left Complex.ofReal_zero⟩
    have hz := cubicThetaShiftedResidue_window_zero m n hh W ha (le_trans hv.1.le hv.2.le)
    have he : (∫ t : ℝ,g t • J t)=∫ t in Icc a d,g t • J t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hg0 : g t=0 := image_eq_zero_of_notMem_tsupport
        (fun hs => ht ⟨(hgs hs).1.le,(hgs hs).2.le⟩)
      rw [hg0,zero_smul]
    rw [he]
    simpa only [W,CompactlySupportedContinuousMap.coe_mk,ContinuousMap.coe_mk,
      Complex.star_def,Complex.conj_ofReal,Complex.real_smul,J] using hz
  have hzero' : J=ᵐ[volume.restrict (Ioo a d)] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae hzero] with t ht he
    exact he ht
  have he := Measure.eqOn_open_of_ae_eq hzero' isOpen_Ioo hJ continuousOn_const
  have hv0 : (v:ℂ)^3≠0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt (hsub hv)))
  have hval := (div_eq_iff hv0).mp (he hv)
  exact sub_eq_zero.mp (by simpa only [Pi.zero_apply,zero_mul] using hval)

theorem cubicThetaShiftedCoefficient_pointwise (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 1<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      cubicThetaShiftedResidueFactor n h*cubicThetaShiftedPoleRadial h v := by
  apply cubicThetaShiftedCoefficient_on_window m n hh (a:=(v+1)/2) (d:=v+1)
  · linarith
  · constructor <;> linarith

theorem cubicThetaShiftedCoefficient_explicit (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 1<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      cubicThetaResidueScale*((Real.pi:ℂ)/Complex.Gamma (4/3))*
        (if (3:Eisenstein) ∣ h-lambdaE*(n:Eisenstein) then
          9*cubicThetaArithmeticFourierResidue (lambdaE*h) (4/3) else 0)*
        cubicThetaShiftedPoleRadial h v := by
  rw [cubicThetaShiftedCoefficient_pointwise m n hh hv,cubicThetaShiftedResidueFactor,
    cubicThetaRegularizedShiftedFrequency_pole n hh]

end CubicFirstMoment

end

end OAI

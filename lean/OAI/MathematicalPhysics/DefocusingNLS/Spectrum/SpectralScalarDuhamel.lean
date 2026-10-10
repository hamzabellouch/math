import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreenRepresentation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarTransferKernel
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellIntegral

namespace OAI

/-! Initial-value variation of constants on a closed shell. The frame and the
solution need differential equations only in the interior. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralScalarDuhamelIntegral (R : ℝ) (D U : ℝ → ℂ × ℂ)
    (W : ℂ) (f : ℝ → ℂ) (r : ℝ) : ℂ × ℂ :=
  (∫ t in R..r, (D t).1*f t/W) • U r -
    (∫ t in R..r, (U t).1*f t/W) • D r

theorem spectralScalarDuhamel_representation
    (R E : ℝ) (D U q : ℝ → ℂ × ℂ) (V f : ℝ → ℂ) (W : ℂ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hfc : ContinuousOn f (Icc R E))
    (hW : W≠0) (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t)=W)
    (hD : ∀ t ∈ Ioo R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Ioo R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Ioo R E, HasDerivAt q (spectralScalarField (V t) (q t)+(0,f t)) t)
    (r : ℝ) (hr : r ∈ Icc R E) :
    q r=(spectralScalarWronskian (q R) (U R)/W) • D r +
      (spectralScalarWronskian (D R) (q R)/W) • U r +
      spectralScalarDuhamelIntegral R D U W f r := by
  let A := fun t => spectralScalarWronskian (D t) (q t)/W
  let B := fun t => spectralScalarWronskian (q t) (U t)/W
  have hAc : ContinuousOn A (Icc R E) := by dsimp only [A,spectralScalarWronskian]; fun_prop
  have hBc : ContinuousOn B (Icc R E) := by dsimp only [B,spectralScalarWronskian]; fun_prop
  have hAD (t : ℝ) (ht : t ∈ Ioo R E) : HasDerivAt A ((D t).1*f t/W) t := by
    have hd : HasDerivAt D (spectralScalarField (V t) (D t)+(0,0)) t := by
      simpa only [Prod.mk_zero_zero,add_zero] using hD t ht
    simpa only [zero_mul,sub_zero] using
      (spectralScalarWronskian_forced D q (V t) 0 (f t) t hd (hq t ht)).div_const W
  have hBD (t : ℝ) (ht : t ∈ Ioo R E) : HasDerivAt B (-((U t).1*f t/W)) t := by
    have hu : HasDerivAt U (spectralScalarField (V t) (U t)+(0,0)) t := by
      simpa only [Prod.mk_zero_zero,add_zero] using hU t ht
    apply ((spectralScalarWronskian_forced q U (V t) (f t) 0 t (hq t ht) hu).div_const W).congr_deriv
    ring
  have hs : Icc R r ⊆ Icc R E := Icc_subset_Icc le_rfl hr.2
  have hiA := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 (hAc.mono hs)
    (fun t ht => hAD t ⟨ht.1,ht.2.trans_le hr.2⟩)
    (ContinuousOn.intervalIntegrable_of_Icc hr.1 (((hDc.fst.mul hfc).div_const W).mono hs))
  have hiB := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 (hBc.mono hs)
    (fun t ht => hBD t ⟨ht.1,ht.2.trans_le hr.2⟩)
    (ContinuousOn.intervalIntegrable_of_Icc hr.1 ((((hUc.fst.mul hfc).div_const W).neg).mono hs))
  rw [intervalIntegral.integral_neg] at hiB
  have ha : A r=A R+∫ t in R..r, (D t).1*f t/W := by linear_combination -hiA
  have hb : B r=B R-∫ t in R..r, (U t).1*f t/W := by linear_combination -hiB
  have he := spectralScalarWronskian_decomposition (D r) (U r) (q r) W hW (hdet r hr)
  change B r • D r+A r • U r=q r at he
  rw [ha,hb] at he
  rw [← he]
  dsimp only [A,B,spectralScalarDuhamelIntegral]
  module

theorem spectralScalarDuhamelIntegral_eq_integral
    (R r : ℝ) (hr : R≤ r) (D U : ℝ → ℂ × ℂ) (W : ℂ) (f : ℝ → ℂ)
    (hD : ContinuousOn D (Icc R r)) (hU : ContinuousOn U (Icc R r))
    (hf : ContinuousOn f (Icc R r)) :
    spectralScalarDuhamelIntegral R D U W f r=
      ∫ t in R..r, (f t) • spectralScalarTransferKernel D U W r t := by
  have hA : IntervalIntegrable (fun t => ((D t).1*f t/W) • U r) volume R r :=
    ContinuousOn.intervalIntegrable_of_Icc hr (((hD.fst.mul hf).div_const W).smul continuousOn_const)
  have hB : IntervalIntegrable (fun t => ((U t).1*f t/W) • D r) volume R r :=
    ContinuousOn.intervalIntegrable_of_Icc hr (((hU.fst.mul hf).div_const W).smul continuousOn_const)
  have he (t : ℝ) : (f t) • spectralScalarTransferKernel D U W r t=
      ((D t).1*f t/W) • U r-((U t).1*f t/W) • D r := by
    dsimp only [spectralScalarTransferKernel]
    rw [smul_sub,smul_smul,smul_smul]
    congr 1 <;> congr 1 <;> ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub hA hB,intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const]
  rfl

end DefocusingNLS

end OAI

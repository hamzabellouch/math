import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreenIntegral

namespace OAI

/-! Mixed endpoint variation of constants. Every actual scalar solution is
recovered from its left outgoing coefficient, right Dirichlet coefficient,
and the Green integral, without a separate uniqueness assumption. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralScalarWronskian_forced
    (D U : ℝ → ℂ × ℂ) (V f g : ℂ) (r : ℝ)
    (hD : HasDerivAt D (spectralScalarField V (D r)+(0,f)) r)
    (hU : HasDerivAt U (spectralScalarField V (U r)+(0,g)) r) :
    HasDerivAt (fun t => spectralScalarWronskian (D t) (U t))
      ((D r).1*g-f*(U r).1) r := by
  have hD₁ := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hD
  have hD₂ := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hD
  have hU₁ := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hU
  have hU₂ := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hU
  apply ((hD₁.mul hU₂).sub (hD₂.mul hU₁)).congr_deriv
  dsimp only [spectralScalarField,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd',Function.comp_apply,Prod.fst_add,Prod.snd_add]
  ring

theorem spectralScalarWronskian_decomposition (D U q : ℂ × ℂ) (W : ℂ)
    (hW : W≠0) (hdet : spectralScalarWronskian D U=W) :
    (spectralScalarWronskian q U/W) • D +
      (spectralScalarWronskian D q/W) • U=q := by
  have he : D.1*U.2-D.2*U.1=W := hdet
  apply Prod.ext
  · dsimp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul,spectralScalarWronskian]
    field_simp
    linear_combination q.1*he
  · dsimp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul,spectralScalarWronskian]
    field_simp
    linear_combination q.2*he

theorem spectralScalarGreen_representation
    (R E : ℝ) (D U q : ℝ → ℂ × ℂ) (V f : ℝ → ℂ) (W : ℂ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hfc : ContinuousOn f (Icc R E))
    (hW : W≠0) (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t)=W)
    (hD : ∀ t ∈ Icc R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Icc R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Icc R E, HasDerivAt q (spectralScalarField (V t) (q t)+(0,f t)) t)
    (r : ℝ) (hr : r ∈ Icc R E) :
    q r=(spectralScalarWronskian (q E) (U E)/W) • D r +
      (spectralScalarWronskian (D R) (q R)/W) • U r +
      spectralScalarGreenIntegral R E D U W f r := by
  let A := fun t => spectralScalarWronskian (D t) (q t)/W
  let B := fun t => spectralScalarWronskian (q t) (U t)/W
  have hAc : ContinuousOn A (Icc R E) := by dsimp only [A,spectralScalarWronskian]; fun_prop
  have hBc : ContinuousOn B (Icc R E) := by dsimp only [B,spectralScalarWronskian]; fun_prop
  have hAD : ∀ t ∈ Icc R E, HasDerivAt A ((D t).1*f t/W) t := by
    intro t ht
    have hd : HasDerivAt D (spectralScalarField (V t) (D t)+(0,0)) t := by
      simpa only [Prod.mk_zero_zero,add_zero] using hD t ht
    simpa only [zero_mul,sub_zero] using
      (spectralScalarWronskian_forced D q (V t) 0 (f t) t hd (hq t ht)).div_const W
  have hBD : ∀ t ∈ Icc R E, HasDerivAt B (-((U t).1*f t/W)) t := by
    intro t ht
    have hu : HasDerivAt U (spectralScalarField (V t) (U t)+(0,0)) t := by
      simpa only [Prod.mk_zero_zero,add_zero] using hU t ht
    have hh := (spectralScalarWronskian_forced q U (V t) (f t) 0 t (hq t ht) hu).div_const W
    convert hh using 1
    ring
  have hsubL : Icc R r ⊆ Icc R E := Icc_subset_Icc le_rfl hr.2
  have hsubR : Icc r E ⊆ Icc R E := Icc_subset_Icc hr.1 le_rfl
  have hiA := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 (hAc.mono hsubL)
    (fun t ht => hAD t ⟨ht.1.le,ht.2.le.trans hr.2⟩)
    (ContinuousOn.intervalIntegrable_of_Icc hr.1 (((hDc.fst.mul hfc).div_const W).mono hsubL))
  have hiB := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.2 (hBc.mono hsubR)
    (fun t ht => hBD t ⟨hr.1.trans ht.1.le,ht.2.le⟩)
    (ContinuousOn.intervalIntegrable_of_Icc hr.2 ((((hUc.fst.mul hfc).div_const W).neg).mono hsubR))
  rw [intervalIntegral.integral_neg] at hiB
  have ha : A r=A R+∫ t in R..r, (D t).1*f t/W := by linear_combination -hiA
  have hb : B r=B E+∫ t in r..E, (U t).1*f t/W := by linear_combination hiB
  have he := spectralScalarWronskian_decomposition (D r) (U r) (q r) W hW (hdet r hr)
  change B r • D r+A r • U r=q r at he
  rw [ha,hb] at he
  rw [← he]
  dsimp only [A,B,spectralScalarGreenIntegral]
  module

end DefocusingNLS

end OAI

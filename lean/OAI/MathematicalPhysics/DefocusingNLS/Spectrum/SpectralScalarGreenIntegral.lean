import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreen

namespace OAI

/-! The actual integral solution of the scalar inhomogeneous boundary problem. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralScalarGreenIntegral (R E : ℝ) (D U : ℝ → ℂ × ℂ)
    (W : ℂ) (f : ℝ → ℂ) (r : ℝ) : ℂ × ℂ :=
  (∫ t in R..r, (D t).1*f t/W) • U r +
    (∫ t in r..E, (U t).1*f t/W) • D r

theorem spectralScalarGreenIntegral_hasDerivAt
    (R E : ℝ) (D U : ℝ → ℂ × ℂ) (W V : ℂ) (f : ℝ → ℂ) (r : ℝ)
    (hDc : Continuous D) (hUc : Continuous U) (hfc : Continuous f)
    (hW : W≠0) (hdet : spectralScalarWronskian (D r) (U r)=W)
    (hD : HasDerivAt D (spectralScalarField V (D r)) r)
    (hU : HasDerivAt U (spectralScalarField V (U r)) r) :
    HasDerivAt (spectralScalarGreenIntegral R E D U W f)
      (spectralScalarField V (spectralScalarGreenIntegral R E D U W f r)+(0,f r)) r := by
  have hA : Continuous (fun t => (D t).1*f t/W) := (hDc.fst.mul hfc).div_const W
  have hB : Continuous (fun t => (U t).1*f t/W) := (hUc.fst.mul hfc).div_const W
  exact spectralScalarGreen_variation D U
    (fun s => ∫ t in R..s, (D t).1*f t/W)
    (fun s => ∫ t in s..E, (U t).1*f t/W) V W (f r) r hW hdet hD hU
    (intervalIntegral.integral_hasDerivAt_right (hA.intervalIntegrable R r)
      hA.stronglyMeasurable.stronglyMeasurableAtFilter hA.continuousAt)
    (intervalIntegral.integral_hasDerivAt_left (hB.intervalIntegrable r E)
      hB.stronglyMeasurable.stronglyMeasurableAtFilter hB.continuousAt)

theorem spectralScalarGreenIntegral_left (R E : ℝ) (D U : ℝ → ℂ × ℂ)
    (W : ℂ) (f : ℝ → ℂ) (hD : (D R).1=0) :
    (spectralScalarGreenIntegral R E D U W f R).1=0 := by
  simp only [spectralScalarGreenIntegral,intervalIntegral.integral_same,zero_smul,
    zero_add,Prod.smul_fst,smul_eq_mul,hD,mul_zero]

theorem spectralScalarGreenIntegral_right (R E : ℝ) (D U : ℝ → ℂ × ℂ)
    (W beta : ℂ) (f : ℝ → ℂ) (hU : (U E).2=beta*(U E).1) :
    (spectralScalarGreenIntegral R E D U W f E).2=
      beta*(spectralScalarGreenIntegral R E D U W f E).1 := by
  simp only [spectralScalarGreenIntegral,intervalIntegral.integral_same,zero_smul,
    add_zero,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,hU]
  ring

end DefocusingNLS

end OAI

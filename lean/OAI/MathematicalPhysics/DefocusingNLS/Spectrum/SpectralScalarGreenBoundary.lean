import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreenRepresentation

namespace OAI

/-! The forced scalar solution separates into its prescribed left value,
the outgoing right error, and the Dirichlet Green correction. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralScalar_left_coefficient (D U q : ℂ × ℂ) (W : ℂ)
    (hD : D.1=0) (hU : U.1≠0) (hW : W≠0)
    (hdet : spectralScalarWronskian D U=W) :
    spectralScalarWronskian D q/W=q.1/U.1 := by
  have he : -D.2*U.1=W := by simpa only [spectralScalarWronskian,hD,zero_mul,zero_sub,neg_mul] using hdet
  dsimp only [spectralScalarWronskian]
  rw [hD,zero_mul,zero_sub]
  apply (div_eq_div_iff hW hU).mpr
  linear_combination q.1*he

theorem spectralScalar_right_coefficient (q U : ℂ × ℂ) (beta W : ℂ)
    (hU : U.2=beta*U.1) :
    spectralScalarWronskian q U/W=(-U.1/W)*(q.2-beta*q.1) := by
  dsimp only [spectralScalarWronskian]
  rw [hU]
  ring

theorem spectralScalarGreen_boundary_representation
    (R E : ℝ) (D U q : ℝ → ℂ × ℂ) (V f : ℝ → ℂ) (W beta : ℂ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hfc : ContinuousOn f (Icc R E))
    (hW : W≠0) (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t)=W)
    (hD : ∀ t ∈ Icc R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Icc R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Icc R E, HasDerivAt q (spectralScalarField (V t) (q t)+(0,f t)) t)
    (hDR : (D R).1=0) (hUR : (U R).1≠0) (hUE : (U E).2=beta*(U E).1)
    (r : ℝ) (hr : r ∈ Icc R E) :
    q r=((q R).1/(U R).1) • U r+
      ((-((U E).1)/W)*((q E).2-beta*(q E).1)) • D r+
      spectralScalarGreenIntegral R E D U W f r := by
  have he := spectralScalarGreen_representation R E D U q V f W hDc hUc hqc hfc
    hW hdet hD hU hq r hr
  rw [spectralScalar_left_coefficient (D R) (U R) (q R) W hDR hUR hW
    (hdet R ⟨le_rfl,hr.1.trans hr.2⟩),
    spectralScalar_right_coefficient (q E) (U E) beta W hUE] at he
  simpa only [add_comm] using he

end DefocusingNLS

end OAI

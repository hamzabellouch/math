import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreenBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm

namespace OAI

/-! Norm control of the exact outgoing Robin error in the scalar Green representation. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralShellNorm_right_error (k : ℝ) (U D : ℂ × ℂ) (W error : ℂ) :
    spectralShellNorm k (((-U.1/W)*error) • D)=
      ‖error‖*spectralShellNorm k ((U.1/W) • D) := by
  simp only [spectralShellNorm_smul,norm_mul,norm_div,norm_neg]
  ring

theorem spectralScalarGreen_boundary_norm
    (R E r k : ℝ) (hr : r ∈ Icc R E) (hk : 0≤ k)
    (D U q : ℝ → ℂ × ℂ) (V f : ℝ → ℂ) (W beta : ℂ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hfc : ContinuousOn f (Icc R E))
    (hW : W≠0) (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t)=W)
    (hD : ∀ t ∈ Icc R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Icc R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Icc R E, HasDerivAt q (spectralScalarField (V t) (q t)+(0,f t)) t)
    (hDR : (D R).1=0) (hUR : (U R).1≠0) (hUE : (U E).2=beta*(U E).1) :
    spectralShellNorm k (q r-((q R).1/(U R).1) • U r)≤
      ‖(q E).2-beta*(q E).1‖*spectralShellNorm k (((U E).1/W) • D r)+
        spectralShellNorm k (spectralScalarGreenIntegral R E D U W f r) := by
  have he := spectralScalarGreen_boundary_representation R E D U q V f W beta
    hDc hUc hqc hfc hW hdet hD hU hq hDR hUR hUE r hr
  have he' : q r-((q R).1/(U R).1) • U r=
      ((-((U E).1)/W)*((q E).2-beta*(q E).1)) • D r+
        spectralScalarGreenIntegral R E D U W f r := by rw [he]; abel
  rw [he']
  exact (spectralShellNorm_add_le k hk _ _).trans_eq
    (congrArg (fun s => s+spectralShellNorm k (spectralScalarGreenIntegral R E D U W f r))
      (spectralShellNorm_right_error k (U E) (D r) W ((q E).2-beta*(q E).1)))

/-- Quantitative absorption form, with a separately bounded remote error
and the small Green correction. -/
theorem spectralShellNorm_boundary_absorption
    (k B eta G M : ℝ) (heta : 0≤ eta) (hM : 0≤ M)
    (q diagonal D U : ℂ × ℂ) (W error : ℂ) (correction : ℂ × ℂ)
    (hk : 0≤ k)
    (he : q-diagonal=((-U.1/W)*error) • D+correction)
    (hremote : spectralShellNorm k ((U.1/W) • D)≤ B)
    (herror : ‖error‖≤ eta*M) (hgreen : spectralShellNorm k correction≤ G*M) :
    spectralShellNorm k (q-diagonal)≤(eta*B+G)*M := by
  rw [he]
  have hn := spectralShellNorm_nonneg k hk ((U.1/W) • D)
  calc
    _ ≤ spectralShellNorm k (((-U.1/W)*error) • D)+spectralShellNorm k correction :=
      spectralShellNorm_add_le k hk _ _
    _ = ‖error‖*spectralShellNorm k ((U.1/W) • D)+spectralShellNorm k correction := by
      rw [spectralShellNorm_right_error]
    _ ≤ (eta*M)*B+G*M := add_le_add (mul_le_mul herror hremote hn (mul_nonneg heta hM)) hgreen
    _ = _ := by ring

end DefocusingNLS

end OAI

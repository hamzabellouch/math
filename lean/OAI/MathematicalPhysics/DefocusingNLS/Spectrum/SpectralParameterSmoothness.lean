import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralParameterGrowthEquation

namespace OAI

/-! Smoothness of the actual inhomogeneous circular parameter equation. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralCoupledParameterField (ν νp νm eta : ℂ) (m : ℕ)
    (t : ℝ) (w : (ℂ × ℂ) × (E₄ × E₄)) : (ℂ × ℂ) × (E₄ × E₄) :=
  (radialExteriorODEField ν m t w.1,
    (circularLeadingField t w.2.1+circularBoundedField νp νm eta m w.1.1 w.2.1,
     circularLeadingField t w.2.2+circularBoundedField νp νm eta m w.1.1 w.2.2+
       circularPointSlopeCLM νp νm 0 w.2.1))

theorem spectralCoupledParameterField_contDiff (ν νp νm eta : ℂ) (m : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (spectralCoupledParameterField ν νp νm eta m)) := by
  have he : ContDiff ℝ ∞ (fun z : ℝ × ((ℂ × ℂ) × (E₄ × E₄)) =>
      ((Real.exp (2*z.1)/2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)).div_const 2)
  have hstar : ContDiff ℝ ∞ (star : ℂ → ℂ) := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff
  unfold Function.uncurry spectralCoupledParameterField radialExteriorODEField
    circularLeadingField circularBoundedField spectralDiagonalCoefficient
    spectralCrossCoefficient oddPowerNonlinearity circularPointSlopeCLM
  simp only [LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk]
  fun_prop

theorem spectralParameter_solution_contDiffOn (ν νp νm eta : ℂ) (m : ℕ)
    (q : ℝ → ℂ × ℂ) (Y Z : ℝ → E₄) (L : ℝ)
    (hq : ∀ t, L<t → HasDerivAt q (radialExteriorODEField ν m t (q t)) t)
    (hY : ∀ t, L<t → HasDerivAt Y (circularLeadingField t (Y t)+
      circularBoundedField νp νm eta m (q t).1 (Y t)) t)
    (hZ : ∀ t, L<t → HasDerivAt Z (circularLeadingField t (Z t)+
      circularBoundedField νp νm eta m (q t).1 (Z t)+circularPointSlopeCLM νp νm 0 (Y t)) t) :
    ContDiffOn ℝ ∞ Z (Ioi L) := by
  have hs : ContDiffOn ℝ ∞ (fun t => (q t,(Y t,Z t))) (Ioi L) := by
    intro r hr
    change L<r at hr
    have hI : Icc ((r+L)/2) (r+1) ⊆ Ioi L := fun t ht => by
      change L<t
      linarith [ht.1]
    have hF := (spectralCoupledParameterField_contDiff ν νp νm eta m).contDiffOn
      (s := Icc ((r+L)/2) (r+1) ×ˢ (univ : Set ((ℂ × ℂ) × (E₄ × E₄))))
    have hh := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤) hF
      (fun t ht => ((hq t (hI ht)).prodMk ((hY t (hI ht)).prodMk (hZ t (hI ht)))).hasDerivWithinAt)
      (fun _ _ => mem_univ _)
    exact (hh r ⟨by linarith,by linarith⟩).contDiffAt
      (Icc_mem_nhds (by linarith) (by linarith)) |>.contDiffWithinAt
  exact hs.snd.snd

end DefocusingNLS

end OAI

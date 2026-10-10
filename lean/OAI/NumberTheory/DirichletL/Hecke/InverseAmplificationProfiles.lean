import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEndpoint
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Set Filter Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def twistProfile (W : ℝ→ℂ) (σ freq x : ℝ) : ℂ := W x*(x : ℂ)^(-shift σ freq)

theorem twistProfile_support (W : ℝ→ℂ) (σ freq : ℝ) :
    Function.support (twistProfile W σ freq)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [twistProfile,hw])

theorem polynomial_twistProfile (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) :
    polynomial χ inv (twistProfile W σ freq) D 0 0=polynomial χ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp [summand,twistProfile,HeckeDyadic.shift,mul_assoc]

theorem twistProfile_smooth (W : ℝ→ℂ) (σ freq a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (twistProfile W σ freq) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0<x
  · have he : twistProfile W σ freq =ᶠ[nhds x]
        (fun y : ℝ => W y*Complex.exp ((Real.log y : ℂ)*(-shift σ freq))) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      unfold twistProfile
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
        ←Complex.ofReal_log hy.le]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    apply hW.contDiffAt.mul
    apply Complex.contDiff_exp.contDiffAt.comp x
    have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne')
    exact hl.mul contDiffAt_const
  · have hxa : x<a := lt_of_le_of_lt (le_of_not_gt hx) ha
    have he : twistProfile W σ freq =ᶠ[nhds x] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hxa] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [twistProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he

end SevenEighths.HeckeInverseAmplification

end

end OAI

import OAI.Analysis.LipschitzHilbert.Fourier.HilbertCutoffProfile
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! Differentiating the actual annular multiplier gives a dyadic difference
of a single compactly supported smooth profile. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertSign_deriv_plateau (x : ℝ) : deriv hilbertSmoothSign x*
    (verticalBinPlateauReal x-verticalBinPlateauReal (2*x))=0 := by
  by_cases hx : |x|≤1/2
  · have hx1 : |x|≤1 := by linarith
    have hx2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_one x hx1,verticalBinPlateauReal_one (2*x) hx2]
    ring
  · rw [hilbertSmoothSign_deriv_zero x (le_of_lt (lt_of_not_ge hx)),zero_mul]

theorem hilbertSign_dilation_deriv (x : ℝ) :
    hilbertSmoothSign x*deriv verticalBinPlateauReal (2*x)=
      hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x) := by
  by_cases hx : |x|≤1/2
  · have hx2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_deriv_zero (2*x) (Or.inl hx2)]
    ring
  · have hxabs : 1/2≤|x| := le_of_lt (lt_of_not_ge hx)
    rcases le_abs.mp hxabs with hp | hn
    · rw [hilbertSmoothSign_pos x hp,hilbertSmoothSign_pos (2*x) (by linarith)]
    · rw [hilbertSmoothSign_neg x (by linarith),hilbertSmoothSign_neg (2*x) (by linarith)]

theorem hilbertAnnularSymbol_hasDerivAt (x : ℝ) :
    HasDerivAt hilbertAnnularSymbol
      (-(Real.pi:ℂ)*Complex.I*(hilbertCutoffDerivative x-2*hilbertCutoffDerivative (2*x))) x := by
  have hs := ((contDiff_infty_iff_deriv.mp hilbertSmoothSign_smooth).1 x).hasDerivAt
  have hc (s : ℝ) := ((contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).1 s).hasDerivAt
  have hc2 := (hc (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hd := (hs.mul ((hc x).sub hc2)).ofReal_comp.const_mul (-(Real.pi:ℂ)*Complex.I)
  convert hd using 1
  · rfl
  · change -(Real.pi:ℂ)*Complex.I*
      (↑(hilbertSmoothSign x*deriv verticalBinPlateauReal x)-
        2*↑(hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x))) = _
    simp only [Pi.sub_apply,Function.comp_apply]
    rw [hilbertSign_deriv_plateau,zero_add]
    have heq : hilbertSmoothSign x*(deriv verticalBinPlateauReal x-
        deriv verticalBinPlateauReal (2*x)*(2*1))=
        hilbertSmoothSign x*deriv verticalBinPlateauReal x-
          2*(hilbertSmoothSign (2*x)*deriv verticalBinPlateauReal (2*x)) := by
      rw [←hilbertSign_dilation_deriv]
      ring
    rw [heq]
    push_cast
    ring

theorem hilbertAnnularSymbol_deriv (x : ℝ) :
    deriv hilbertAnnularSymbol x=
      -(Real.pi:ℂ)*Complex.I*(hilbertCutoffDerivative x-2*hilbertCutoffDerivative (2*x)) :=
  (hilbertAnnularSymbol_hasDerivAt x).deriv

end LipschitzHilbert.PacketRepresentation

end

end OAI

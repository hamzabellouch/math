import OAI.Analysis.LipschitzHilbert.Estimates.HilbertTimeProfile
import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelScaling

namespace OAI

/-! The smooth finite Hilbert multiplier has a uniform bound obtained
from an exact telescoping identity, independently of the scale count. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def hilbertFrequencySign (x : ℝ) : ℂ := if 0≤x then 1 else -1

theorem hilbertFrequencySign_pos_mul (a x : ℝ) (ha : 0<a) :
    hilbertFrequencySign (a*x)=hilbertFrequencySign x := by
  unfold hilbertFrequencySign
  by_cases hx : 0≤x
  · rw [ite_eq_left hx,ite_eq_left (mul_nonneg ha.le hx)]
  · rw [ite_eq_right hx,ite_eq_right (not_le.mpr (mul_neg_of_pos_of_neg ha (lt_of_not_ge hx)))]

theorem hilbertAnnularSymbol_sign (x : ℝ) :
    hilbertAnnularSymbol x=-(Real.pi:ℂ)*Complex.I*
      (hilbertFrequencySign x*(verticalBinPlateau x-verticalBinPlateau (2*x))) := by
  change -(Real.pi:ℂ)*Complex.I*↑(hilbertSmoothSign x*
    (verticalBinPlateauReal x-verticalBinPlateauReal (2*x)))=_
  by_cases hs : |x|≤1/2
  · have h1 : |x|≤1 := by linarith
    have h2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    rw [verticalBinPlateauReal_one x h1,verticalBinPlateauReal_one (2*x) h2,
      verticalBinPlateau_one x h1,verticalBinPlateau_one (2*x) h2]
    simp
  · have hne : x≠0 := by intro hz; subst x; norm_num at hs
    by_cases hp : 0<x
    · have hx : 1/2≤x := by rw [abs_of_pos hp] at hs; linarith
      rw [hilbertSmoothSign_pos x hx,hilbertFrequencySign,ite_eq_left hp.le]
      simp only [one_mul,Complex.ofReal_sub]
      rfl
    · have hx : x≤-(1/2) := by rw [abs_of_nonpos (le_of_not_gt hp)] at hs; linarith
      rw [hilbertSmoothSign_neg x hx,hilbertFrequencySign,ite_eq_right (by linarith)]
      simp only [neg_one_mul,Complex.ofReal_neg,Complex.ofReal_sub]
      rfl

def hilbertFiniteSymbol (N : ℕ) (L : ℝ) (hL : 0<L) : SchwartzMap ℝ ℂ :=
  ∑ j : Fin N, dilatedSlopeWindow hilbertAnnularSymbol (L/(2:ℝ)^j.val)
    (ne_of_gt (div_pos hL (pow_pos (by norm_num) j.val)))

theorem hilbertFiniteSymbol_apply (N : ℕ) (L : ℝ) (hL : 0<L) (eta : ℝ) :
    hilbertFiniteSymbol N L hL eta=-(Real.pi:ℂ)*Complex.I*hilbertFrequencySign eta*
      (verticalBinPlateau ((2*L)/(2:ℝ)^N*eta)-verticalBinPlateau ((2*L)*eta)) := by
  have hterm (j : ℕ) : hilbertAnnularSymbol (L/(2:ℝ)^j*eta)=
      (-(Real.pi:ℂ)*Complex.I*hilbertFrequencySign eta)*
      (verticalBinPlateau ((2*L)/(2:ℝ)^(j+1)*eta)-verticalBinPlateau ((2*L)/(2:ℝ)^j*eta)) := by
    rw [hilbertAnnularSymbol_sign]
    have hp : 0<L/(2:ℝ)^j := div_pos hL (pow_pos (by norm_num) j)
    have hsign : hilbertFrequencySign (L/(2:ℝ)^j*eta)=hilbertFrequencySign eta :=
      hilbertFrequencySign_pos_mul _ _ hp
    have h1 : L/(2:ℝ)^j*eta=(2*L)/(2:ℝ)^(j+1)*eta := by rw [pow_succ]; field_simp
    have h2 : 2*(L/(2:ℝ)^j*eta)=(2*L)/(2:ℝ)^j*eta := by ring
    rw [hsign,h1]
    rw [←h1,h2]
    ring
  simp only [hilbertFiniteSymbol,sum_apply,dilatedSlopeWindow_apply,hterm]
  rw [←Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    verticalBinPlateau ((2*L)/(2:ℝ)^(j+1)*eta)-verticalBinPlateau ((2*L)/(2:ℝ)^j*eta)) N]
  rw [Finset.sum_range_sub (fun j : ℕ =>
    verticalBinPlateau ((2*L)/(2:ℝ)^j*eta))]
  simp only [pow_zero,div_one]

theorem hilbertFiniteSymbol_norm (N : ℕ) (L : ℝ) (hL : 0<L) (eta : ℝ) :
    ‖hilbertFiniteSymbol N L hL eta‖≤Real.pi := by
  rw [hilbertFiniteSymbol_apply]
  have hdiff : ‖verticalBinPlateau ((2*L)/(2:ℝ)^N*eta)-verticalBinPlateau ((2*L)*eta)‖≤1 := by
    change ‖((verticalBinPlateauReal ((2*L)/(2:ℝ)^N*eta):ℂ)-
      (verticalBinPlateauReal ((2*L)*eta):ℂ))‖≤1
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have h1 := verticalBinPlateauReal_range ((2*L)/(2:ℝ)^N*eta)
    have h2 := verticalBinPlateauReal_range ((2*L)*eta)
    exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩
  have hsign : ‖hilbertFrequencySign eta‖≤1 := by
    unfold hilbertFrequencySign
    split_ifs <;> norm_num
  simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_I,mul_one]
  exact (mul_le_mul_of_nonneg_left hdiff (mul_nonneg Real.pi_pos.le (norm_nonneg _))).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsign Real.pi_pos.le)

end LipschitzHilbert.PacketRepresentation

end

end OAI

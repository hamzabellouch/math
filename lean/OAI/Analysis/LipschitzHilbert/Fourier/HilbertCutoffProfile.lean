import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinPlateau
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace OAI

/-! The fixed smooth annular Hilbert multiplier and its cutoff derivative.
All profiles are constructed, rather than supplied as analytic inputs. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def hilbertSmoothSign (x : ℝ) : ℝ :=
  Real.smoothTransition (2*x+1)-Real.smoothTransition (1-2*x)

theorem hilbertSmoothSign_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) hilbertSmoothSign := by
  unfold hilbertSmoothSign
  fun_prop

theorem hilbertSmoothSign_pos (x : ℝ) (hx : 1/2≤x) : hilbertSmoothSign x=1 := by
  simp [hilbertSmoothSign,Real.smoothTransition.one_of_one_le (show 1≤2*x+1 by linarith),
    Real.smoothTransition.zero_of_nonpos (show 1-2*x≤0 by linarith)]

theorem hilbertSmoothSign_neg (x : ℝ) (hx : x≤-(1/2)) : hilbertSmoothSign x= -1 := by
  simp [hilbertSmoothSign,Real.smoothTransition.zero_of_nonpos (show 2*x+1≤0 by linarith),
    Real.smoothTransition.one_of_one_le (show 1≤1-2*x by linarith)]

theorem hilbertSmoothSign_range (x : ℝ) : -1≤hilbertSmoothSign x ∧ hilbertSmoothSign x≤1 := by
  unfold hilbertSmoothSign
  constructor <;> linarith [Real.smoothTransition.nonneg (2*x+1),
    Real.smoothTransition.le_one (2*x+1),Real.smoothTransition.nonneg (1-2*x),
    Real.smoothTransition.le_one (1-2*x)]

theorem hilbertSmoothSign_deriv_zero (x : ℝ) (hx : 1/2≤|x|) :
    deriv hilbertSmoothSign x=0 := by
  rcases le_abs.mp hx with hx | hx
  · apply IsLocalMax.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hilbertSmoothSign_pos x hx]
    exact (hilbertSmoothSign_range y).2
  · apply IsLocalMin.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hilbertSmoothSign_neg x (by linarith)]
    exact (hilbertSmoothSign_range y).1

theorem verticalBinPlateauReal_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) verticalBinPlateauReal := by
  unfold verticalBinPlateauReal
  fun_prop

theorem verticalBinPlateauReal_range (x : ℝ) :
    0≤verticalBinPlateauReal x ∧ verticalBinPlateauReal x≤1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem verticalBinPlateauReal_one (x : ℝ) (hx : |x|≤1) : verticalBinPlateauReal x=1 := by
  have h := verticalBinPlateau_one x hx
  change (verticalBinPlateauReal x:ℂ)=1 at h
  exact_mod_cast h

theorem verticalBinPlateauReal_deriv_zero (x : ℝ) (hx : |x|≤1 ∨ 2≤|x|) :
    deriv verticalBinPlateauReal x=0 := by
  rcases hx with hx | hx
  · apply IsLocalMax.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [verticalBinPlateauReal_one x hx]
    exact (verticalBinPlateauReal_range y).2
  · have hz : verticalBinPlateauReal x=0 := by
      apply verticalBinPlateauReal_zero
      rcases le_abs.mp hx with hx | hx
      · exact Or.inr hx
      · exact Or.inl (by linarith)
    apply IsLocalMin.deriv_eq_zero
    apply Filter.Eventually.of_forall
    intro y
    rw [hz]
    exact (verticalBinPlateauReal_range y).1

def hilbertCutoffDerivative : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => ((hilbertSmoothSign x*deriv verticalBinPlateauReal x : ℝ) : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2:ℝ) 2))
    intro x hx
    have ha : 2≤|x| := by
      by_contra hn
      have h := abs_lt.mp (lt_of_not_ge hn)
      exact hx ⟨h.1.le,h.2.le⟩
    simp only [f,verticalBinPlateauReal_deriv_zero x (Or.inr ha),mul_zero,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply Complex.ofRealCLM.contDiff.comp
    apply hilbertSmoothSign_smooth.mul
    exact (contDiff_infty_iff_deriv.mp verticalBinPlateauReal_smooth).2)

def hilbertAnnularSymbol : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => -(Real.pi:ℂ)*Complex.I*
    ((hilbertSmoothSign x*(verticalBinPlateauReal x-verticalBinPlateauReal (2*x)) : ℝ) : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2:ℝ) 2))
    intro x hx
    have ha : 2≤|x| := by
      by_contra hn
      have h := abs_lt.mp (lt_of_not_ge hn)
      exact hx ⟨h.1.le,h.2.le⟩
    have hz (s : ℝ) (hs : 2≤|s|) : verticalBinPlateauReal s=0 := by
      apply verticalBinPlateauReal_zero
      rcases le_abs.mp hs with hs | hs
      · exact Or.inr hs
      · exact Or.inl (by linarith)
    have ha2 : 2≤|2*x| := by rw [abs_mul]; norm_num; linarith
    simp only [f,hz x ha,hz (2*x) ha2,sub_self,mul_zero,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply contDiff_const.mul
    apply Complex.ofRealCLM.contDiff.comp
    exact hilbertSmoothSign_smooth.mul (verticalBinPlateauReal_smooth.sub
      (verticalBinPlateauReal_smooth.comp (show ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : ℝ => 2*x) by fun_prop))))

theorem hilbertAnnularSymbol_support (x : ℝ) (hx : hilbertAnnularSymbol x≠0) :
    1/2≤|x| ∧ |x|≤2 := by
  constructor
  · by_contra hn
    have ha := (lt_of_not_ge hn).le
    have ha1 : |x|≤1 := by linarith
    have ha2 : |2*x|≤1 := by rw [abs_mul]; norm_num; linarith
    apply hx
    change -(Real.pi:ℂ)*Complex.I*↑(hilbertSmoothSign x*
      (verticalBinPlateauReal x-verticalBinPlateauReal (2*x)))=0
    rw [verticalBinPlateauReal_one x ha1,verticalBinPlateauReal_one (2*x) ha2]
    simp
  · by_contra hn
    have ha : 2≤|x| := (lt_of_not_ge hn).le
    have hz (s : ℝ) (hs : 2≤|s|) : verticalBinPlateauReal s=0 := by
      apply verticalBinPlateauReal_zero
      rcases le_abs.mp hs with hs | hs
      · exact Or.inr hs
      · exact Or.inl (by linarith)
    have ha2 : 2≤|2*x| := by rw [abs_mul]; norm_num; linarith
    apply hx
    change -(Real.pi:ℂ)*Complex.I*↑(hilbertSmoothSign x*
      (verticalBinPlateauReal x-verticalBinPlateauReal (2*x)))=0
    rw [hz x ha,hz (2*x) ha2]
    simp

end LipschitzHilbert.PacketRepresentation

end

end OAI

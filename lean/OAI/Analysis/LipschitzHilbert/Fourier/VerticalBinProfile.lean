import OAI.Analysis.LipschitzHilbert.Estimates.SlopePartition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace OAI

/-! A fixed real smooth bin profile whose squared translates sum to one.
The trigonometric construction avoids a variable normalization denominator. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

def binSquareStep (x : ℝ) : ℝ := (Real.sin (Real.pi/2*Real.smoothTransition x))^2

def verticalBinProfileReal (x : ℝ) : ℝ :=
  Real.sin (Real.pi/2*Real.smoothTransition (x+1))*Real.cos (Real.pi/2*Real.smoothTransition x)

theorem binSquareStep_zero (x : ℝ) (hx : x≤0) : binSquareStep x=0 := by
  simp [binSquareStep,Real.smoothTransition.zero_of_nonpos hx]

theorem binSquareStep_one (x : ℝ) (hx : 1≤x) : binSquareStep x=1 := by
  simp [binSquareStep,Real.smoothTransition.one_of_one_le hx]

theorem verticalBinProfileReal_sq (x : ℝ) :
    (verticalBinProfileReal x)^2=binSquareStep (x+1)-binSquareStep x := by
  by_cases hx : x≤0
  · simp [verticalBinProfileReal,binSquareStep,Real.smoothTransition.zero_of_nonpos hx]
  · have hx1 : 1≤x+1 := by linarith
    have hs := Real.sin_sq_add_cos_sq (Real.pi/2*Real.smoothTransition x)
    simp only [verticalBinProfileReal,binSquareStep,Real.smoothTransition.one_of_one_le hx1,
      mul_one,Real.sin_pi_div_two,one_mul,one_pow]
    linarith

theorem verticalBinProfileReal_zero (x : ℝ) (hx : x≤-1 ∨ 1≤x) : verticalBinProfileReal x=0 := by
  rcases hx with hx | hx
  · simp [verticalBinProfileReal,Real.smoothTransition.zero_of_nonpos (show x+1≤0 by linarith)]
  · simp [verticalBinProfileReal,Real.smoothTransition.one_of_one_le hx]

def verticalBinProfile : SchwartzMap ℝ ℂ :=
  let f := fun x : ℝ => (verticalBinProfileReal x : ℂ)
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1))
    intro x hx
    have hxx : x≤-1 ∨ 1≤x := by
      by_cases h : -1≤x
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun hx1 => hx ⟨h,hx1⟩)))
      · exact Or.inl (le_of_lt (lt_of_not_ge h))
    simp only [f,verticalBinProfileReal_zero x hxx,Complex.ofReal_zero]
  hc.toSchwartzMap (by
    apply Complex.ofRealCLM.contDiff.comp
    change ContDiff ℝ (↑(⊤:ℕ∞)) verticalBinProfileReal
    unfold verticalBinProfileReal
    fun_prop)

theorem verticalBinProfile_apply (x : ℝ) : verticalBinProfile x=(verticalBinProfileReal x : ℂ) := rfl

theorem verticalBinProfile_real (x : ℝ) : star (verticalBinProfile x)=verticalBinProfile x := by
  simp only [verticalBinProfile_apply,Complex.star_def,Complex.conj_ofReal]

theorem verticalBinProfile_support (x : ℝ) (hx : verticalBinProfile x≠0) : |x|≤1 := by
  by_contra h
  have ha : 1 < |x| := lt_of_not_ge h
  have hxx : x≤-1 ∨ 1≤x := by
    rcases lt_or_ge x 0 with hn | hp
    · rw [abs_of_neg hn] at ha
      exact Or.inl (by linarith)
    · rw [abs_of_nonneg hp] at ha
      exact Or.inr ha.le
  exact hx (by simp only [verticalBinProfile_apply,verticalBinProfileReal_zero x hxx,Complex.ofReal_zero])

theorem verticalBinProfileReal_sum_sq (x : ℝ) (N : ℕ) :
    (∑ n∈Finset.range N, (verticalBinProfileReal (x-(n:ℝ)))^2)=
      binSquareStep (x+1)-binSquareStep (x+1-N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,verticalBinProfileReal_sq]
    push_cast
    rw [show x+1-((N:ℝ)+1)=x-N by ring,show x-N+1=x+1-N by ring]
    ring

theorem verticalBinProfile_sum_sq (K : ℕ) (x : ℝ) (hx : |x|≤K) :
    (∑ n∈Finset.range (2*K+1), (verticalBinProfile (x+K-(n:ℝ)))^2)=1 := by
  simp only [verticalBinProfile_apply,←Complex.ofReal_pow,←Complex.ofReal_sum]
  rw [verticalBinProfileReal_sum_sq]
  have hb := abs_le.mp hx
  rw [binSquareStep_one _ (by linarith),binSquareStep_zero _ (by push_cast; linarith)]
  norm_num

end LipschitzHilbert.PacketRepresentation

end

end OAI

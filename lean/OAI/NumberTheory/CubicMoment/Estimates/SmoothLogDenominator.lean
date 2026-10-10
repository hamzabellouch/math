import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! Smooth, globally defined extensions of the logarithmic denominator
weights. The extension equals the literal reciprocal on the application
range, so no pole can interfere with parameter-uniform differentiation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CubicFirstMoment

def positiveSmoothExtension (c x : ℝ) : ℝ :=
  Real.smoothTransition (2*x/c-1)*x +
    (1-Real.smoothTransition (2*x/c-1))*c

lemma positiveSmoothExtension_eq {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    positiveSmoothExtension c x = x := by
  have h : 1 ≤ 2*x/c-1 := by
    have hd : 2 ≤ 2*x/c := (le_div_iff₀ hc).mpr (by linarith)
    linarith
  simp [positiveSmoothExtension,Real.smoothTransition.one_of_one_le h]

lemma positiveSmoothExtension_pos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 < positiveSmoothExtension c x := by
  by_cases hx : x ≤ c/2
  · have h : 2*x/c-1 ≤ 0 := by
      have hh : 2*x ≤ c := by linarith
      have hd := (div_le_one hc).mpr hh
      linarith
    simpa [positiveSmoothExtension,Real.smoothTransition.zero_of_nonpos h] using hc
  · have hx0 : 0 < x := by linarith
    have h0 := Real.smoothTransition.nonneg (2*x/c-1)
    have h1 := Real.smoothTransition.le_one (2*x/c-1)
    dsimp [positiveSmoothExtension]
    by_cases he : Real.smoothTransition (2*x/c-1) = 0
    · simpa [he] using hc
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne h0 (Ne.symm he)) hx0)
        (mul_nonneg (by linarith) hc.le)

lemma positiveSmoothExtension_smooth (c : ℝ) :
    ContDiff ℝ ∞ (positiveSmoothExtension c) := by
  unfold positiveSmoothExtension
  fun_prop

def smoothReciprocal (c x : ℝ) : ℝ := (positiveSmoothExtension c x)⁻¹

lemma smoothReciprocal_smooth {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ∞ (smoothReciprocal c) :=
  (positiveSmoothExtension_smooth c).inv (fun x => (positiveSmoothExtension_pos hc x).ne')

lemma smoothReciprocal_eq {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    smoothReciprocal c x = x⁻¹ := by
  simp only [smoothReciprocal,positiveSmoothExtension_eq hc hx]

def smoothLog (x : ℝ) : ℝ := Real.log (positiveSmoothExtension 1 x)

lemma smoothLog_smooth : ContDiff ℝ ∞ smoothLog :=
  (positiveSmoothExtension_smooth 1).log
    (fun x => (positiveSmoothExtension_pos (by norm_num) x).ne')

lemma smoothLog_eq {x : ℝ} (hx : 1 ≤ x) : smoothLog x = Real.log x := by
  simp only [smoothLog,positiveSmoothExtension_eq (by norm_num : (0:ℝ) < 1) hx]

/-- Parameters are the normalized scale logarithm and inverse logarithm
of the outer length. Both range over a compact rectangle. -/
def logDenominatorWeight (c : ℝ) (w : ℝ → ℂ) (p : ℝ × ℝ) (x : ℝ) : ℂ :=
  (smoothReciprocal c (p.1+p.2*smoothLog x):ℂ)*w x

lemma logDenominatorWeight_joint_smooth {c : ℝ} (hc : 0 < c)
    {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => logDenominatorWeight c w z.1 z.2) := by
  have hL := smoothLog_smooth.comp
    (contDiff_snd : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => z.2))
  have hD : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      z.1.1+z.1.2*smoothLog z.2) := by fun_prop
  have hr := (smoothReciprocal_smooth hc).comp hD
  have hrC : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      (smoothReciprocal c (z.1.1+z.1.2*smoothLog z.2):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  exact hrC.mul (hw.comp contDiff_snd)

lemma logDenominatorWeight_eq {c : ℝ} (hc : 0 < c) (w : ℝ → ℂ)
    {p : ℝ × ℝ} (ha : c ≤ p.1) (ht : 0 ≤ p.2) {x : ℝ} (hx : 1 ≤ x) :
    logDenominatorWeight c w p x = w x/(p.1+p.2*Real.log x:ℝ) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hd : c ≤ p.1+p.2*Real.log x := by nlinarith
  rw [logDenominatorWeight,smoothLog_eq hx,smoothReciprocal_eq hc hd]
  push_cast
  ring

end CubicFirstMoment

end

end OAI

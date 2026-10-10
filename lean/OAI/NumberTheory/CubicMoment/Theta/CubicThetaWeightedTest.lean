import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateIntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

/-! Compact tests with the hyperbolic first-derivative weight v^-1.
The support stays away from the singular boundary v=0. -/
noncomputable section
open Set
namespace CubicFirstMoment

def cubicThetaHeightInverse (p : ℂ × ℝ) : ℂ := (p.2⁻¹ : ℝ)

def cubicThetaWeightedTest (φ : ℂ × ℝ → ℂ) (p : ℂ × ℝ) : ℂ :=
  star (φ p)*cubicThetaHeightInverse p

lemma cubicThetaHeightInverse_regular :
    ContDiffOn ℝ 1 cubicThetaHeightInverse {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  have h : ContDiffAt ℝ 1 cubicThetaHeightInverse p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_snd.inv hp.ne')
  exact h.contDiffWithinAt

lemma cubicThetaWeightedTest_support (φ : ℂ × ℝ → ℂ) :
    tsupport (cubicThetaWeightedTest φ)⊆tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  apply subset_tsupport
  intro h
  exact hp (by simp [cubicThetaWeightedTest,h])

lemma cubicThetaWeightedTest_regular {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hp : tsupport φ⊆{p : ℂ × ℝ | 0<p.2}) : ContDiff ℝ 1 (cubicThetaWeightedTest φ) := by
  have hbar : ContDiff ℝ 1 (fun p => star (φ p)) := by
    exact Complex.conjCLE.contDiff.comp hφ
  have hsupport : tsupport (fun p => star (φ p))⊆tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport φ)
    intro p hp
    apply subset_tsupport
    intro h
    exact hp (by simp [h])
  exact cubicThetaPositiveProduct_contDiff hbar (hsupport.trans hp) cubicThetaHeightInverse_regular

lemma cubicThetaWeightedTest_compact {φ : ℂ × ℝ → ℂ} (hc : HasCompactSupport φ) :
    HasCompactSupport (cubicThetaWeightedTest φ) :=
  hc.of_isClosed_subset isClosed_closure (cubicThetaWeightedTest_support φ)

lemma cubicThetaHeightInverse_axis (k : CubicThetaAxis) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaAxisFirst k cubicThetaHeightInverse p=
      match k with
      | .x => 0
      | .y => 0
      | .height => -((p.2^2)⁻¹ : ℝ) := by
  cases k with
  | x => simp [cubicThetaAxisFirst,cubicThetaCoordinateLine,cubicThetaHeightInverse,cubicThetaCoordinateCenter,cubicThetaCartesianPoint]
  | y => simp [cubicThetaAxisFirst,cubicThetaCoordinateLine,cubicThetaHeightInverse,cubicThetaCoordinateCenter,cubicThetaCartesianPoint]
  | height =>
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt p.2 (hasDerivAt_inv hp.ne')
    simpa only [cubicThetaAxisFirst,cubicThetaCoordinateLine,cubicThetaHeightInverse,
      cubicThetaCoordinateCenter,cubicThetaCartesianPoint,ContinuousLinearMap.toSpanSingleton_apply,
      Complex.ofRealCLM_apply,Function.comp_def,Complex.ofReal_neg] using h.deriv

lemma cubicThetaWeightedTest_axis (k : CubicThetaAxis) {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaAxisFirst k (cubicThetaWeightedTest φ) p=
      star (cubicThetaAxisFirst k φ p)*cubicThetaHeightInverse p+
        star (φ p)*cubicThetaAxisFirst k cubicThetaHeightInverse p := by
  let c := cubicThetaCoordinateCenter k p.1.re p.1.im p.2
  let line := cubicThetaCoordinateLine k p.1.re p.1.im p.2
  have hl : DifferentiableAt ℝ line c := by
    cases k with
    | x =>
      change DifferentiableAt ℝ (fun t : ℝ => ((t:ℂ)+(p.1.im:ℂ)*Complex.I,p.2)) c
      fun_prop
    | y =>
      change DifferentiableAt ℝ (fun t : ℝ => ((p.1.re:ℂ)+(t:ℂ)*Complex.I,p.2)) c
      fun_prop
    | height =>
      change DifferentiableAt ℝ (fun t : ℝ => ((p.1.re:ℂ)+(p.1.im:ℂ)*Complex.I,t)) c
      fun_prop
  have he : line c=p := by
    dsimp [line,c]
    rw [cubicThetaCoordinateLine_center,cubicThetaCartesianPoint_self]
  have hdφ : DifferentiableAt ℝ (fun t => φ (line t)) c :=
    DifferentiableAt.fun_comp' (f:=line) c (hφ.differentiable one_ne_zero (line c)) hl
  have hdv : DifferentiableAt ℝ (fun t => cubicThetaHeightInverse (line t)) c := by
    have hr := (cubicThetaHeightInverse_regular.contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).differentiableAt (by norm_num)
    rw [← he] at hr
    exact DifferentiableAt.fun_comp' (f:=line) c hr hl
  have hstar := hdφ.hasDerivAt.star
  have h := hstar.mul hdv.hasDerivAt
  have hv := h.deriv
  change deriv (fun t => star (φ (line t))*cubicThetaHeightInverse (line t)) c=_ at hv
  change deriv (fun t => star (φ (line t))*cubicThetaHeightInverse (line t)) c=_
  rw [hv,he]
  rfl

end CubicFirstMoment

end

end OAI

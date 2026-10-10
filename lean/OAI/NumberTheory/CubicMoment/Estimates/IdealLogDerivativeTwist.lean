import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerPositivity
import OAI.NumberTheory.CubicMoment.Estimates.HeckeSmoothDual
import OAI.NumberTheory.CubicMoment.Estimates.RamifiedIdealParts
import OAI.NumberTheory.CubicMoment.Estimates.GramMellinTwist
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace OAI

/-! Vertical translation and the zero-free positivity inequality for the
literal complete ideal series. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

def idealNormTwist (χ : EisensteinIdealExponent → ℂ) (t : ℝ)
    (ν : EisensteinIdealExponent) : ℂ := χ ν*mellinPhase t (idealExponentNorm ν)

lemma idealNormTwist_norm (χ : EisensteinIdealExponent → ℂ) (t : ℝ)
    (ν : EisensteinIdealExponent) : ‖idealNormTwist χ t ν‖=‖χ ν‖ := by
  simp only [idealNormTwist,norm_mul,mellinPhase_norm,mul_one]

lemma idealNormTwist_zero (χ : EisensteinIdealExponent → ℂ) (t : ℝ)
    (hχ0 : χ 0=1) : idealNormTwist χ t 0=1 := by
  simp [idealNormTwist,hχ0,idealExponentNorm,idealExponentGenerator,mellinPhase]

lemma idealNormTwist_add (χ : EisensteinIdealExponent → ℂ) (t : ℝ)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) (ν κ : EisensteinIdealExponent) :
    idealNormTwist χ t (ν+κ)=idealNormTwist χ t ν*idealNormTwist χ t κ := by
  simp only [idealNormTwist,hχadd,idealExponentNorm_add,
    mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
  ring

lemma idealNormTwist_sq (χ : EisensteinIdealExponent → ℂ) (t : ℝ) :
    (fun ν => (idealNormTwist χ t ν)^2)=idealNormTwist (fun ν => (χ ν)^2) (2*t) := by
  funext ν
  simp only [idealNormTwist,pow_two]
  rw [show 2*t=t+t by ring,mellinPhase_add_height]
  ring

lemma idealNormTwist_logDeriv (χ : EisensteinIdealExponent → ℂ) (t : ℝ) (s : ℂ) :
    logDeriv (normDirichletSeries (idealNormTwist χ t) idealExponentNorm) s=
      logDeriv (normDirichletSeries χ idealExponentNorm) (s-(t:ℂ)*Complex.I) := by
  have he : normDirichletSeries (idealNormTwist χ t) idealExponentNorm=
      fun z => normDirichletSeries χ idealExponentNorm (z-(t:ℂ)*Complex.I) := by
    funext z
    exact twisted_normDirichletSeries χ t z
  rw [he,logDeriv_apply,deriv_comp_sub_const]
  rfl

theorem idealLogDeriv_vertical_341_nonneg (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3*(-logDeriv (normDirichletSeries (fun _ => 1) idealExponentNorm) (σ:ℂ)).re+
      4*(-logDeriv (normDirichletSeries χ idealExponentNorm) ((σ:ℂ)+(t:ℂ)*Complex.I)).re+
      (-logDeriv (normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm)
        ((σ:ℂ)+(2*t:ℝ)*Complex.I)).re := by
  have h := idealLogDeriv_341_nonneg (idealNormTwist χ (-t))
    (fun ν => by simpa only [idealNormTwist_norm] using hχ ν)
    (idealNormTwist_zero χ (-t) hχ0) (idealNormTwist_add χ (-t) hχadd) hσ
  rw [idealNormTwist_sq,idealNormTwist_logDeriv,idealNormTwist_logDeriv] at h
  have e1 : (σ:ℂ)-(-t:ℝ)*Complex.I=(σ:ℂ)+(t:ℂ)*Complex.I := by
    push_cast
    ring
  have e2 : (σ:ℂ)-(2*(-t):ℝ)*Complex.I=(σ:ℂ)+(2*t:ℝ)*Complex.I := by
    push_cast
    ring
  simpa only [e1,e2] using h

lemma idealSeries_logDeriv_eq {χ : EisensteinIdealExponent → ℂ} {L : ℂ → ℂ}
    (hseries : ∀ z : ℂ, 1 < z.re → L z=normDirichletSeries χ idealExponentNorm z)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv L s=logDeriv (normDirichletSeries χ idealExponentNorm) s := by
  have he : L =ᶠ[𝓝 s] normDirichletSeries χ idealExponentNorm := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact hseries z hz
  exact (logDeriv_congr_nhds he).self_of_nhds

end CubicFirstMoment

end

end OAI

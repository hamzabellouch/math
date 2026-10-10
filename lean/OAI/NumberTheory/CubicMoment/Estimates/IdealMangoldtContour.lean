import OAI.NumberTheory.CubicMoment.Estimates.IdealMangoldtMellin
import OAI.NumberTheory.CubicMoment.Estimates.FiniteMellinContour

namespace OAI

/-! The finite contour identity for the actual ideal von Mangoldt
Mellin integrand. Nonvanishing on the box is supplied by the proved
Hecke zero-free region, before estimating its edges. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def idealMangoldtMellinIntegrand (L : ℂ → ℂ) (W : ℝ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin W s*(X:ℂ)^s*(-logDeriv L s)

lemma idealMangoldtMellinIntegrand_differentiableOn
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X a b T : ℝ} (hX : 0 < X)
    (hn : ∀ s ∈ finiteMellinBox a b T, L s ≠ 0) :
    DifferentiableOn ℂ (idealMangoldtMellinIntegrand L W X) (finiteMellinBox a b T) := by
  let _ : NeZero (X:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
  have hm := smooth_mellin_entire W hW hpos hsm.continuous
  intro s hs
  have hl : AnalyticAt ℂ (logDeriv L) s :=
    (hL.analyticAt s).deriv.div (hL.analyticAt s) (hn s hs)
  exact (((hm s).mul ((differentiable_const_cpow_of_neZero (X:ℂ)) s)).mul
    hl.differentiableAt.neg).differentiableWithinAt

theorem idealMangoldt_finite_contour_bound
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X a b T H : ℝ} (hX : 0 < X)
    (hab : a ≤ b) (hT : 0 ≤ T)
    (hn : ∀ s ∈ finiteMellinBox a b T, L s ≠ 0)
    (hTop : ∀ x ∈ Icc a b, ‖idealMangoldtMellinIntegrand L W X (x+(T:ℂ)*Complex.I)‖ ≤ H)
    (hBot : ∀ x ∈ Icc a b, ‖idealMangoldtMellinIntegrand L W X (x-(T:ℂ)*Complex.I)‖ ≤ H) :
    ‖(∫ y in -T..T, idealMangoldtMellinIntegrand L W X (b+(y:ℂ)*Complex.I))-
      (∫ y in -T..T, idealMangoldtMellinIntegrand L W X (a+(y:ℂ)*Complex.I))‖ ≤
        2*H*(b-a) :=
  finite_mellin_shift_bound hab hT _
    (idealMangoldtMellinIntegrand_differentiableOn hL W hW hpos hsm hX hn) hTop hBot

end CubicFirstMoment

end

end OAI

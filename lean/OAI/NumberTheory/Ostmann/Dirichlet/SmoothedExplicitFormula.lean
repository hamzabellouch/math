import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitTruncation
import OAI.NumberTheory.Ostmann.ZeroDensity.Target

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped Topology BigOperators SchwartzMap ContDiff
namespace Ostmann.Dirichlet

def compactRealSchwartz (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : 𝓢(ℝ, ℂ) :=
  (hc.comp_left (show Complex.ofReal 0 = 0 from Complex.ofReal_zero)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)

@[simp] theorem compactRealSchwartz_apply (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (x : ℝ) : compactRealSchwartz φ hφ hc x = (φ x : ℂ) := rfl

theorem smoothError_eq_compactRealSchwartz {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (X : ℝ) :
    Ostmann.ZeroDensity.smoothError χ φ X =
      ∑' n : ℕ, χ n*(ArithmeticFunction.vonMangoldt n:ℂ)*
        compactRealSchwartz φ hφ hc ((n:ℝ)/X) := by
  simp only [Ostmann.ZeroDensity.smoothError, ite_eq_right hχ, sub_zero,
    compactRealSchwartz_apply]
  apply tsum_congr
  intro n
  ring

theorem exists_smoothed_explicit_formula (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (X T : ℝ),
      Real.exp 2 ≤ X → 2 ≤ T →
      ‖Ostmann.ZeroDensity.smoothError χ φ X‖ ≤
        C*(upperZeroWeight χ hχ (T+1) X A +
          Real.sqrt X*((q:ℝ)*(T+2))^7 +
          X*((q:ℝ)*(T+2))^7/T^A*(1+Real.log X)^7) := by
  obtain ⟨C,hC,hbound⟩ := exists_smoothed_explicit_truncation (compactRealSchwartz φ hφ hc) A
  refine ⟨C,hC,?_⟩
  intro q _ χ hχ X T hX hT
  rw [smoothError_eq_compactRealSchwartz χ hχ φ hφ hc]
  exact hbound q χ hχ X T hX hT

end Ostmann.Dirichlet

end

end OAI

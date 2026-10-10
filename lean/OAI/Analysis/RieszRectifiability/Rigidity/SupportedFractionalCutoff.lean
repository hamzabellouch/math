import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.FinitePairingCancellation
import OAI.Analysis.RieszRectifiability.Rigidity.FiniteFractionalHeightPairing
import OAI.Analysis.RieszRectifiability.Kernel.SupportedKernelDecomposition

namespace OAI

/-!
# Fractional cutoffs for supported tests

Separation between the test support and the exterior region makes the cutoff
inactive in cross terms. The cutoff increment is also the closed-exterior
indicator of the full increment, giving its integrability and its equality
with the truncated fractional Schwartz test.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter SchwartzMap

theorem supported_fractional_cutoff_cross {d : ℕ} (m : ℕ) (ε H R : ℝ)
    (a x y : Ambient d) (g : Ambient d → ℂ)
    (hnear : g x ≠ 0 → dist x a ≤ H) (hfar : y ∈ closedExterior a R)
    (hsep : ε + H ≤ R) :
    symmetricFractionalCutoffKernel m ε (x, y) • g x =
      inverseDistancePow (m + 1) x y • g x := by
  by_cases hg : g x = 0
  · rw [hg]
    exact (smul_zero _).trans (smul_zero _).symm
  · have hy : R ≤ dist a y := hfar
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    have hd : ε ≤ dist x y := by linarith [hnear hg]
    simp only [symmetricFractionalCutoffKernel, ite_eq_left hd]

theorem supported_fractional_cutoff_cross_swap {d : ℕ} (m : ℕ) (ε H R : ℝ)
    (a x y : Ambient d) (g : Ambient d → ℂ)
    (hnear : g x ≠ 0 → dist x a ≤ H) (hfar : y ∈ closedExterior a R)
    (hsep : ε + H ≤ R) :
    symmetricFractionalCutoffKernel m ε (y, x) • g x =
      inverseDistancePow (m + 1) x y • g x := by
  rw [show symmetricFractionalCutoffKernel m ε (y, x) =
      symmetricFractionalCutoffKernel m ε (x, y) from
    symmetricFractionalCutoffKernel_swap m ε (x, y)]
  exact supported_fractional_cutoff_cross m ε H R a x y g hnear hfar hsep

theorem test_zero_outside_localization {d : ℕ} (g : Ambient d → ℂ)
    (a : Ambient d) (H R : ℝ) (hHR : H < R)
    (hnear : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    ∀ y ∈ (ball a R)ᶜ, g y = 0 := by
  intro y hy
  by_contra hgy
  have hh := hnear y hgy
  have hf : R ≤ dist y a := by simpa only [mem_compl_iff, mem_ball, not_lt] using! hy
  linarith

theorem fractional_cutoff_increment_eq_indicator {d : ℕ} (m : ℕ) (ε : ℝ)
    (g : Ambient d → ℂ) (x : Ambient d) :
    (fun y => symmetricFractionalCutoffKernel m ε (x, y) • (g x - g y)) =
      (closedExterior x ε).indicator (fun y => inverseDistancePow (m + 1) x y • (g x - g y)) := by
  funext y
  by_cases h : ε ≤ dist x y
  · rw [indicator_of_mem (show y ∈ closedExterior x ε from h)]
    simp only [symmetricFractionalCutoffKernel, ite_eq_left h]
  · rw [indicator_of_notMem (show y ∉ closedExterior x ε from h)]
    simp only [symmetricFractionalCutoffKernel, ite_eq_right h]
    exact zero_smul ℝ (g x - g y)

theorem fractional_cutoff_increment_integrable (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    Integrable (fun y => symmetricFractionalCutoffKernel (p + 1) ε (x, y) • (g x - g y)) volume := by
  rw [fractional_cutoff_increment_eq_indicator]
  exact (integrable_indicator_iff (closedExterior_measurable x ε)).2
    (fractionalSchwartz_single_increment_integrable p ε hε g x)

theorem fractional_cutoff_increment_integral (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    (∫ y, symmetricFractionalCutoffKernel (p + 1) ε (x, y) • (g x - g y)) =
      fractionalSchwartzTruncatedTest p ε g x := by
  rw [fractional_cutoff_increment_eq_indicator, integral_indicator (closedExterior_measurable x ε)]
  exact (fractionalSchwartzTruncatedTest_eq_single_increment p ε hε g x).symm

end

end RieszRectifiability

end OAI

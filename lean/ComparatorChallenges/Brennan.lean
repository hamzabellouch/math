import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Brennan

def disk : Set ℂ := Metric.ball 0 1

def UnivalentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ Set.InjOn f U

def Schlicht (f : ℂ → ℂ) : Prop :=
  UnivalentOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1

def integralMean (f : ℂ → ℂ) (t r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi,
    ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ t

def beta (f : ℂ → ℂ) (t : ℝ) : EReal :=
  Filter.limsup (fun r : ℝ =>
    ((Real.log (integralMean f t r) / Real.log (1 / (1 - r)) : ℝ) : EReal))
    (𝓝[<] (1 : ℝ))

def spectrum (t : ℝ) : EReal :=
  sSup {b | ∃ f : ℂ → ℂ, Schlicht f ∧ beta f t = b}

def SphericalBoundaryNontrivial (W : Set ℂ) : Prop :=
  Set.Nontrivial (frontier (((↑) : ℂ → OnePoint ℂ) '' W))

def MainStatement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ f : ℂ → ℂ, Schlicht f →
    ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
      integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε)) ∧
  spectrum (-2) = 1 ∧
  (∀ W : Set ℂ, IsOpen W → IsConnected W → SimplyConnectedSpace W →
    SphericalBoundaryNontrivial W → ∀ φ : ℂ → ℂ,
      DifferentiableOn ℂ φ W → Set.BijOn φ W disk →
      ∀ s : ℝ, 4 / 3 < s → s < 4 →
        IntegrableOn (fun z => ‖deriv φ z‖ ^ s) W volume) ∧
  (∀ f : ℂ → ℂ, UnivalentOn f disk → ∀ t : ℝ,
    -2 < t → t < 2 / 3 →
      IntegrableOn (fun z => ‖deriv f z‖ ^ t) disk volume)

theorem main_theorem : MainStatement := by
  sorry

end Brennan
end

end OAI

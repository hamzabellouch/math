import OAI.Probability.ThorpResults.SignedBudget
import OAI.Probability.ThorpResults.FullDensity
import OAI.Probability.ThorpResults.Mixing

namespace OAI

noncomputable section
open Filter

namespace ThorpResults
open ThorpNine.Harmonic.Thorp
open ThorpNine.Harmonic.Thorp.Specht
open ThorpNine.Harmonic.Thorp.LowPlanes

attribute [local instance] hsNorm hsInner hsFinite

def FrameMain : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop, ∀ start : _root_.OAI.Thorp.State d,
    _root_.OAI.Thorp.tv (_root_.OAI.Thorp.lawFrom d (32800 * d) start) (_root_.OAI.Thorp.uniform d) < ε

def InformationMain : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
    ∀ k : ℕ, 8 * k ≤ 7 * 2 ^ d →
    ∀ (start : _root_.OAI.Thorp.State d) (labels : _root_.OAI.Thorp.LabelList d k),
      _root_.OAI.Thorp.listTV (256 * d) start labels < ε) ∧
  (∀ᶠ d : ℕ in atTop,
    ∀ k : ℕ, 16 * k ≤ 15 * 2 ^ d →
    ∀ (start : _root_.OAI.Thorp.State d) (labels : _root_.OAI.Thorp.LabelList d k),
      _root_.OAI.Thorp.listTV (1024 * d) start labels ≤
        Real.rpow ((2 : ℝ) ^ d) (-(3 : ℝ) / 2)) ∧
  (Tendsto (fun d : ℕ => _root_.OAI.Thorp.distance d (2048 * d)) atTop (nhds 0) ∧
    ∀ (d : ℕ) (start : _root_.OAI.Thorp.State d),
      _root_.OAI.Thorp.tv (_root_.OAI.Thorp.lawFrom d (2048 * d) start) (_root_.OAI.Thorp.uniform d) =
        _root_.OAI.Thorp.distance d (2048 * d))

def SpectrumMain : Prop :=
  ∃ p : ℝ, 0 < p ∧ ∀ d : ℕ, 1 ≤ d →
    regularTrace d (2 * p) ≤ 1 + 1 / 16 ∧
    ∀ M : ℕ, p ≤ M → ∀ σ : Equiv.Perm (Card d), sweepDistance d M σ ≤ 1 / 8

def SignedMain : Prop :=
  ∀ η κ : ℝ, 0 < η → ∃ r : ℕ, 1 ≤ r ∧ ∀ d : ℕ, 1 ≤ d →
    ∀ (μ : Shapes (2 ^ d)) (α β γ : YoungDiagram),
      α.card + β.card + γ.card = 2 ^ d →
      logWeightedMoment d r μ ≤
        ((budgetCoefficient η d * signedEntropy α β +
          remainderBudget κ d γ.card : ℝ) : EReal)

def DegreeSavingMain : Prop :=
  ∃ r : ℕ, Even r ∧ 2 ≤ r ∧ ∃ η : ℝ, 0 < η ∧
    ∀ d (μ : Shapes (2 ^ d)),
      (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) *
        (LinearMap.trace ℂ (hilbertSpace μ.1)
          ((Q d μ * star (Q d μ)) ^ r).toLinearMap).re ≤
        (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) ^ (1 - η)

def FullDensityMain : Prop :=
  ∃ v : ℕ, 1 ≤ v ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
    ∀ σ : Equiv.Perm (Card d), densityL2SquaredFrom d (v * d) σ < ε

def ForwardMixingMain : Prop :=
  ∃ v : ℕ, 1 ≤ v ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
    ∀ σ : Equiv.Perm (Card d), sweepDistance d v σ < ε

def OptimalOrderMain : Prop :=
  Asymptotics.IsTheta atTop (fun d : ℕ => (_root_.OAI.Thorp.mixingTime d : ℝ))
    (fun d : ℕ => Real.log (2 ^ d : ℝ))

end ThorpResults

end

end OAI

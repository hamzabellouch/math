import OAI.NumberTheory.Ostmann.Arithmetic.IdealHistoryNorm
import OAI.NumberTheory.Ostmann.Construction.HistorySmoothBound

namespace OAI

/-! # The ideal norm estimate with the smooth amplitude constructed -/

namespace Ostmann

open scoped BigOperators Classical

theorem idealHistoryNorm_smooth_le {Q : ℕ} [NeZero Q]
    {I : Type*} [Fintype I] (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (S : Finset ℤ) (V n : ℕ) (hp : ∀ i, 3 ≤ p i)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) ≤ (p i : ℝ))
    (data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (d e : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n →
      ∀ i, SpectatorDiagram (p i) n)
    (h₁ h₂ : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n →
      (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) → HistorySmoothData n)
    (A : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n →
      (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) → ℂ)
    (X Δ C K κ : ℝ) (ψhat : ℝ → ℂ)
    (hψ : ∀ t, ‖ψhat t‖ ≤ Real.exp K)
    (hA : ∀ t x y, ‖A t x y‖ ≤ Real.exp κ)
    (hmod₁ : ∀ t x y, (h₁ t x y).ModuliBound X Δ C)
    (hmod₂ : ∀ t x y, (h₂ t x y).ModuliBound X Δ C) :
    idealHistoryNorm p S V n g data d e
      (fun t x y => A t x y *
        ((h₁ t x y).value X ψhat * star ((h₂ t x y).value X ψhat))) ≤
      (Real.exp (-(2 ^ n : ℕ) * Δ + ((2 ^ n : ℕ) * (C + 2 * K) + κ)) *
        (3 : ℝ) ^ (2 ^ n * Fintype.card I)) * arithmeticProductSupportSum S V n data := by
  apply idealHistoryNorm_le p S V n hp g hg henergy data d e _ _ (Real.exp_pos _).le
  intro t x y
  exact full_smooth_factor_exp_le (h₁ t x y) (h₂ t x y) X Δ C K κ ψhat (A t x y)
    hψ (hA t x y) (hmod₁ t x y) (hmod₂ t x y)

end Ostmann

end OAI

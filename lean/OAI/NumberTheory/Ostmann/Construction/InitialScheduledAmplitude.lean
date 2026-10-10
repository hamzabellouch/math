import OAI.NumberTheory.Ostmann.Construction.InitialAmplitudePermutation
import OAI.NumberTheory.Ostmann.Construction.InitialScheduledPrior

namespace OAI

/-! # The literal initial amplitude starts the compensation schedule -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplatePrimeAmplitude_initial_schedule {A J : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ a, value a ≠ 0)
    (b d top : ℕ) (cs : List ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Pg : Finset ℕ) (hPg : ∀ p ∈ Pg, p ≠ 0) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    let cells := initialSmallCellList top cs
    let F := movingOriginalLeaf value q
      (initialMovingDataCutoff value b d cells.length cb cd sl sr fallback) g Dq S ψ X lo hi
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G
      0 (cells.length + cells.length) (b + b) Pg ρ
      (initialMovingRegularPrior b cells.length (fun _ => bulk) (fun i => cell (cells.get i)))
      greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G
      0 (scheduledSmallLength cs) (b + b) Pg ρ
      (scheduledRegularPrior cell bulk top cs 0 (b + b)) greg ggiant favorable := by
  intro cells F
  obtain ⟨e, he⟩ := initialMovingRegularPrior_cell_reindex cell bulk top cs b
  rw [he]
  exact movingTemplatePrimeAmplitude_initial_small_equiv value hvalue b d cells.length cb cd
    sl sr fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G Pg hPg ρ
    (scheduledSmallLength cs) (scheduledRegularPrior cell bulk top cs 0 (b + b)) e
    greg ggiant favorable

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationRoles
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceData
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceGaps
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTargetsBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries
open scoped BigOperators

def configurationAnchorPair {k : ℕ} (cfg : SourceConfiguration k) (j : ℕ) : ℝ :=
  if hj : j < k then
    (cfg.1 ⟨j,by omega⟩ : ℝ) + (cfg.1 ⟨k+j,by omega⟩ : ℝ)
  else 0

def configurationTarget {k : ℕ} (logX J : ℝ) (Δ : ℕ → ℝ)
    (cfg : SourceConfiguration k) (j : Fin (k+1)) : ℝ :=
  if j.val < k then
    HigherBiasSourceTargets.pivotTarget k J (configurationAnchorPair cfg) Δ j.val
  else HigherBiasSourceTargets.fillerTarget k logX J (configurationAnchorPair cfg) Δ

def repeatedAnchors (k : ℕ) (small big : ℤ) : Fin (2*k) → ℤ :=
  fun i => if i.val < k then small else big

theorem configurationAnchorPair_repeated {k : ℕ} (small big : ℤ)
    (lists : Fin (k+1) → List ℤ) {j : ℕ} (hj : j < k) :
    configurationAnchorPair (repeatedAnchors k small big,lists) j = (small:ℝ)+big := by
  simp only [configurationAnchorPair,dite_eq_left hj,repeatedAnchors,ite_eq_left hj,
    show ¬k+j<k by omega,ite_false]

def ConfigurationGoodAt {d : Decomposition} {E : Finset ℕ} {δ L : ℝ} {k : ℕ}
    {α β ρ γ c0 : ℝ} (s : SelectedWordSource d E δ L k α β ρ γ c0)
    (c : ℝ) (cfg : SourceConfiguration k) (n : ℤ) : Prop :=
  ∀ i : Fin (configCellCount cfg),
    0 ≤ configCellIndices cfg i ∧
    (configCellIndices cfg i : ℝ) ≤ Real.exp (β*L) ∧
    c/Real.exp (β*L) ≤ primeShellMass
      (boundedRawLogCell s.locations.primes (configCellIndices cfg i)) ∧
    ∃ hp : 0 < primeShellMass
      (boundedRawLogCell s.locations.primes (configCellIndices cfg i)),
      δ/4 ≤ ((primeShellPrior
        (boundedRawLogCell s.locations.primes (configCellIndices cfg i)) hp).cmean
        (fun p => s.family.test p (n:ZMod p.val))).re

structure ConfigurationGeometry {d : Decomposition} {E : Finset ℕ} {δ L : ℝ} {k : ℕ}
    {α β ρ γ c0 : ℝ} (s : SelectedWordSource d E δ L k α β ρ γ c0)
    (c BD : ℝ) (cfg : SourceConfiguration k) : Prop where
  anchors : ∃ small big : ℤ,cfg.1 = repeatedAnchors k small big ∧
    Real.exp s.locations.s < (small:ℝ) ∧ (small:ℝ)+1 ≤ Real.exp (s.locations.s+1) ∧
    Real.exp s.locations.u < (big:ℝ) ∧ (big:ℝ)+1 ≤ Real.exp (s.locations.u+1)
  anchor_bound : ∀ j < k,0 ≤ configurationAnchorPair cfg j ∧
    configurationAnchorPair cfg j ≤ 4*Real.exp s.locations.u
  length_lower : ∀ j,Real.exp ((1/10000:ℝ)*k)/6 ≤ ((cfg.2 j).length:ℝ)
  length_upper : ∀ j,((cfg.2 j).length:ℝ) ≤ 2*Real.exp (2*((1/10000:ℝ)*k))
  target_error : ∀ j,|((cfg.2 j).sum:ℝ) - configurationTarget (Real.log s.locations.X)
    s.J (InitialCharacterScale.gapSchedule BD k L) cfg j| ≤ 6/c
  list_entry_lower : ∀ j,∀ i∈cfg.2 j,Real.exp s.locations.U ≤ (i:ℝ)

end Ostmann.Characters.HigherBiasSource

end

end OAI

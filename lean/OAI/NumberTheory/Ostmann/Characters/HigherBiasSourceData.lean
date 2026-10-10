import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceSelectedWord
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceShellSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Preliminaries Construction HigherBiasSourceWord InitialCharacterScale

structure SourceLocations (E : Finset ℕ) (L : ℝ) (k : ℕ) (α β ρ γ c₀ : ℝ) where
  w : ℝ
  A : ℝ
  B : ℝ
  D : ℝ
  s : ℝ
  U : ℝ
  u : ℝ
  k_pos : 0 < k
  width_lower : γ*L ≤ w
  width_upper : w ≤ (β-α+1)*L
  A_nonneg : 0 ≤ A
  lower_separation : A+2*w ≤ B
  upper_separation : B+2*w ≤ D
  upper_end : D+w ≤ β*L
  bulk_mass : ρ*L ≤ harmonicIntervalMass E B (B+w)
  small_start : A ≤ s
  small_end : s+1 ≤ A+w
  small_mass : c₀ ≤ harmonicIntervalMass E s (s+1)
  grid_start : D ≤ U
  grid_end : U+5*(k:ℝ) ≤ D+w
  top_start : U ≤ u
  top_end : u+1 ≤ U+higherSourceEpsilon*(k:ℝ)
  top_lower : α*L-1 ≤ u
  top_upper : u ≤ β*L
  top_mass : c₀ ≤ harmonicIntervalMass E u (u+1)
  bulk_gap : B+w ≤ u-γ*L
  small_gap : s+1 ≤ u-3*(γ*L)
  rich : ∀ v : ℝ,U ≤ v → v+higherSourceEpsilon*(k:ℝ) ≤ U+5*(k:ℝ) →
    ∃ i : ℕ,v ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ v+higherSourceEpsilon*(k:ℝ) ∧
      c₀ ≤ harmonicIntervalMass E (U+(i:ℝ)) (U+(i:ℝ)+1)

namespace SourceLocations
variable {E : Finset ℕ} {L : ℝ} {k : ℕ} {α β ρ γ c₀ : ℝ}

def X (s : SourceLocations E L k α β ρ γ c₀) : ℕ := higherSourceX k s.u
def Q (s : SourceLocations E L k α β ρ γ c₀) : ℕ := collisionScale 10 s.X
def primes (s : SourceLocations E L k α β ρ γ c₀) : Finset (PrimeUpTo s.Q) := boundedPrimeSet s.Q E
def base (s : SourceLocations E L k α β ρ γ c₀) (i : Fin 3) : Finset (PrimeUpTo s.Q) :=
  boundedInterval s.primes (![s.B,s.s,s.u] i) (![s.B+s.w,s.s+1,s.u+1] i)
def tests (s : SourceLocations E L k α β ρ γ c₀) : Fin (5*k+3) → Finset (PrimeUpTo s.Q) :=
  testedShellFamily s.primes s.base c₀ s.U (Real.log s.X) k
end SourceLocations

structure SelectedWordSource (d : Decomposition) (E : Finset ℕ) (δ L : ℝ)
    (k : ℕ) (α β ρ γ c₀ : ℝ) where
  locations : SourceLocations E L k α β ρ γ c₀
  family : HigherBiasSourceFamily d locations.Q locations.primes δ
  test_mass_pos : ∀ i,0 < primeShellMass (locations.tests i)
  bulk_pos : 0 < primeShellMass (locations.base 0)
  top_pos : 0 < primeShellMass (locations.base 2)
  J : ℤ
  endpoints : Finset ℤ
  window : ∀ n∈endpoints,∃ a∈upperWindow d.A locations.X,(a:ℤ)=n
  bin_lower : (9/10:ℝ)*Real.exp locations.u ≤ (J:ℝ)
  bin_upper : (J:ℝ) ≤ 4*Real.exp locations.u
  cardinal : Real.sqrt locations.X*Real.exp (-selectionCost β (δ/2)*(wordSize k L:ℝ)) ≤ endpoints.card
  word_mean : ∀ n∈endpoints,Real.exp (-selectionCost β (δ/2)*(wordSize k L:ℝ)) ≤
    ‖initialCharacterMean (roleShells (locations.base 0) (locations.base 2) (wordSize k L))
      (roleShells_mass_pos bulk_pos top_pos (wordSize k L))
      (fun _=>familyCharacter family) (fun _=>familyCenter family) (fun _=>familyPhase family)
      (binIndicator J) n‖
  shell_means : ∀ n∈endpoints,∀ i,δ/2 ≤
    ((primeShellPrior (locations.tests i) (test_mass_pos i)).cmean
      (fun p=>family.test p (n:ZMod p.val))).re

end Ostmann.Characters.HigherBiasSource

end

end OAI

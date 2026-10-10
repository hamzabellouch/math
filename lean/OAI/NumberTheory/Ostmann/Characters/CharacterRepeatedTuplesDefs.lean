import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesBasic
import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesPrior

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Characters
open Construction Preliminaries

def characterTupleTest {Q b : ℕ}
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (w : Fin b → PrimeUpTo Q) (n : ℤ) : ℂ :=
  ∏ i, phasedCharacter (χ i (w i).val) (a i (w i).val) (z i (w i).val)
    (n : ZMod (w i).val)

def characterTuplePhysical {Q b : ℕ}
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (X : ℝ) (w : Fin b → PrimeUpTo Q) : ℂ :=
  (∑' n : ℤ, characterTupleTest χ a z w n*SchwartzCutoff.psi ((n : ℝ)/X)) /
    (Real.sqrt X : ℂ)

def characterRepeatedContribution {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (B : (Fin b → PrimeUpTo Q) → ℝ) (X : ℝ) : ℂ := by
  classical
  exact (characterTuplePrior E hE).cmean (fun w =>
    if Function.Injective w then 0 else (B w : ℂ)*characterTuplePhysical χ a z X w)

def characterDistinctContribution {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (B : (Fin b → PrimeUpTo Q) → ℝ) (X : ℝ) : ℂ := by
  classical
  exact (characterTuplePrior E hE).cmean (fun w =>
    if Function.Injective w then (B w : ℂ)*characterTuplePhysical χ a z X w else 0)

theorem character_physical_mean_eq_distinct_add_repeated {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (B : (Fin b → PrimeUpTo Q) → ℝ) (X : ℝ) :
    (characterTuplePrior E hE).cmean (fun w => (B w : ℂ)*characterTuplePhysical χ a z X w) =
      characterDistinctContribution E hE χ a z B X + characterRepeatedContribution E hE χ a z B X := by
  classical
  unfold characterDistinctContribution characterRepeatedContribution FinitePrior.cmean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  dsimp only
  split_ifs <;> ring

end Ostmann.Characters

end

end OAI

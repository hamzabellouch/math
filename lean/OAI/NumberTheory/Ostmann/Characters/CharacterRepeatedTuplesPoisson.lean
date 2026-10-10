import OAI.NumberTheory.Ostmann.Characters.CharacterInitialPhase
import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Characters
open Construction Preliminaries

def characterTupleFourier {Q b : ℕ}
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (X : ℝ) (w : Fin b → PrimeUpTo Q) : ℂ := by
  letI (i : Fin b) : Fact (w i).val.Prime := ⟨primeUpTo_prime (w i)⟩
  exact (∏ i, z i (w i).val)*(Real.sqrt (X/(characterTupleProduct w : ℝ)) : ℂ)*
    (∑' s : ℤ, initialPhase (fun i => (w i).val) (fun i => χ i (w i).val)
      (fun i => a i (w i).val) s *
      𝓕 SchwartzCutoff.psi (-(s : ℝ)*X/(characterTupleProduct w : ℝ)))

theorem characterTuplePhysical_eq_fourier {Q b : ℕ}
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (w : Fin b → PrimeUpTo Q) (hw : Function.Injective w)
    (hχ : ∀ i, χ i (w i).val ≠ 1) {X : ℝ} (hX : 0 < X) :
    characterTuplePhysical χ a z X w = characterTupleFourier χ a z X w := by
  let (i : Fin b) : Fact (w i).val.Prime := ⟨primeUpTo_prime (w i)⟩
  let : NeZero (∏ i, (w i).val) := ⟨(characterTupleProduct_pos w).ne'⟩
  have hcop : Pairwise (fun i j => (w i).val.Coprime (w j).val) := by
    intro i j hij
    exact (Nat.coprime_primes (primeUpTo_prime (w i)) (primeUpTo_prime (w j))).mpr
      (fun h => hij (hw (Subtype.ext h)))
  have hh := initial_character_poisson (fun i => (w i).val) hcop
    (fun i => χ i (w i).val) hχ (fun i => a i (w i).val) SchwartzCutoff.psi hX
  unfold characterTuplePhysical characterTupleTest phasedCharacter
  simp only [Finset.prod_mul_distrib, mul_assoc, tsum_mul_left]
  rw [mul_div_assoc, hh]
  simp only [characterTupleFourier, characterTupleProduct, mul_assoc]

def initialCharacterAmplitude {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (B : (Fin b → PrimeUpTo Q) → ℝ) (X : ℝ) : ℂ := by
  classical
  exact (characterTuplePrior E hE).cmean (fun w =>
    if Function.Injective w then (B w : ℂ)*characterTupleFourier χ a z X w else 0)

theorem characterDistinctContribution_eq_amplitude {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (hχ : ∀ i, ∀ p ∈ E i, χ i p.val ≠ 1)
    (B : (Fin b → PrimeUpTo Q) → ℝ) {X : ℝ} (hX : 0 < X) :
    characterDistinctContribution E hE χ a z B X = initialCharacterAmplitude E hE χ a z B X := by
  classical
  unfold characterDistinctContribution initialCharacterAmplitude FinitePrior.cmean
  apply Finset.sum_congr rfl
  intro w hw
  dsimp only
  by_cases hsupport : ∀ i, w i ∈ E i
  · by_cases hinj : Function.Injective w
    · rw [ite_eq_left hinj, ite_eq_left hinj, characterTuplePhysical_eq_fourier χ a z w hinj
        (fun i => hχ i (w i) (hsupport i)) hX]
    · simp only [ite_eq_right hinj]
  · rw [characterTuplePrior_mass_eq_zero E hE w hsupport]
    simp

end Ostmann.Characters

end

end OAI

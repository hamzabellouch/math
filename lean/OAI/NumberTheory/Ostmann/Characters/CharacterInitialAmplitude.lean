import OAI.NumberTheory.Ostmann.Construction.InitialScheduleRangeAmplitude
import OAI.NumberTheory.Ostmann.Construction.InitialWordPriorIntervals
import OAI.NumberTheory.Ostmann.Characters.CharacterInitialProduct
import OAI.NumberTheory.Ostmann.Characters.CharacterWordIntervals

namespace OAI

/-! # The concrete character intervals start at the original word statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem character_initial_amplitude (k m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ c, Fin (characterCellSize r f c)) ≃ Fin nc)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (cellLo cellHi : (Σ c, Fin (characterCellSize r f c)) → ℕ)
    (hcell : ∀ i q, q ∈ R (cell i) → cellLo i ≤ q ∧ q ≤ cellHi i)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (pivot : ℕ → (Σ v, Fin (characterSize m r f v)))
    (center : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ))
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (logX Δ τ c : ℝ) (hc : 1 ≤ c) (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (N : ℕ) (childBound pivotBound : ℕ → ℕ) (b : Fin (⌊4 * τ⌋₊ + 1))
    (hlo : ∀ v, Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) - c) ≤ ∏ i, cellLo ⟨v, i⟩)
    (hhi : ∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤ Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) + c))
    (hbin : ∀ y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ) :
    let lo := initialWordAtomLower b.val (fun v => ∏ i, cellLo ⟨v, i⟩)
    let hi := initialWordAtomUpper b.val (fun v => ∏ i, cellHi ⟨v, i⟩)
    let C := (Fintype.card (CharacterRole k) : ℝ) * c
    constituentPrimeGuardedAmplitude (characterRole k) (characterSize m r f)
      (fun i => wordCopyCharacter (m + 1) nc χ
        (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i))
      (fun i => primeGaussMultiplier (wordCopyCharacter (m + 1) nc χ
        (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i)))
      pivot 0 P hP
      (fun i => Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i))
      childBound pivotBound (atomIntervalRanges (characterRole k) lo hi)
      (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
        (Real.exp (Δ - C)) (Real.exp (Δ + C)))
      (fun v : Finset.Icc (-(N : ℤ)) (N : ℤ) => (v : ℤ)) center =
    wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) χ center ψ (Real.exp logX) N
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b := by
  intro lo hi C
  apply initial_schedule_word_amplitude_of_range_equiv (characterRole k) m nc
    (characterCellSize r f) cell P hP Q R χ hχ pivot center ψ (Real.exp logX) τ
    (Real.exp (Δ - C)) (Real.exp (Δ + C)) (Real.exp_pos _) heven N childBound pivotBound
    (atomIntervalRanges (characterRole k) lo hi) b
  · intro x hx
    exact initialWordPrior_atomIntervals_equiv (characterRole k) (m + 1) nc b.val
      (characterCellSize r f) cell P Q R cellLo cellHi hcell x hx
  · exact hbin
  · intro x _hx hguard
    have herr := character_word_interval_errors b.val c hc T a
      (characterFillerTarget logX Δ b.val T a)
      (fun v => ∏ i, cellLo ⟨v, i⟩) (fun v => ∏ i, cellHi ⟨v, i⟩) hlo hhi
    have hw := character_initial_product_window k logX Δ b.val c T a lo hi herr.1 herr.2
      (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) hguard
    change (scheduleAtomTotal (characterRole k)
      ⟨0, fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)⟩ : ℝ) / Real.exp logX ∈ _ at hw
    have ht := initial_atom_total (characterRole k)
      (fun v => initialWordSize (m + 1) (characterCellSize r f) v.2)
      (fun i => (x i : ℕ))
    rw [ht] at hw
    exact hw

end Ostmann

end OAI

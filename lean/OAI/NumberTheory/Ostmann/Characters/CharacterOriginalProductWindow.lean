import OAI.NumberTheory.Ostmann.Characters.CharacterInitialAmplitude
import OAI.NumberTheory.Ostmann.Characters.CharacterFullPrimeCells

namespace OAI

/-! # The original fixed-bin product lies in the constructed Poisson window -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_original_product_window (k m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (hcell : ∀ i p, p ∈ R (cell i) → cellLo i ≤ p ∧ p ≤ cellHi i)
    (logX Δ τ c : ℝ) (hc : 1 ≤ c) (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (b : Fin (⌊4 * τ⌋₊ + 1))
    (hlo : ∀ v, Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) - c) ≤ ∏ i, cellLo ⟨v, i⟩)
    (hhi : ∀ v, (∏ i, cellHi ⟨v, i⟩ : ℕ) ≤ Real.exp (characterLogCenter b.val T a
      (characterFillerTarget logX Δ b.val T a) (true, some v) + c))
    (hbin : ∀ y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ)
    (y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P)
    (hy : y ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun i => primeSubsetPrior P (R i))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b) :
    let C := (Fintype.card (CharacterRole k) : ℝ) * c
    (∏ i, (y i : ℝ)) / Real.exp logX ∈
      Set.Icc (Real.exp (Δ - C)) (Real.exp (Δ + C)) := by
  intro C
  let role := characterRole k
  let e := initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell
  let x := fun i => y (e i)
  let lo := initialWordAtomLower b.val (fun v => ∏ i, cellLo ⟨v, i⟩)
  let hi := initialWordAtomUpper b.val (fun v => ∏ i, cellHi ⟨v, i⟩)
  obtain ⟨hb, hp⟩ := (mem_wordCharacterEvent _ _ _ _ y).mp hy
  rw [wordCopyPrimePrior] at hp
  have hx : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) (e i)) (x i)) ≠ 0 := by
    change (∏ i, (fun j => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) j) (y j)) (e i)) ≠ 0
    have he := e.prod_comp (fun j => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) j) (y j))
    intro hz
    exact hp (he.symm.trans hz)
  have hr : ∀ s ∈ initialWordBinRanges role b.val,
      s.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) := by
    have h := (initialWordBinRanges_iff_bin role m nc (characterCellSize r f) cell P hP
      τ b y (hbin y hp).1 (hbin y hp).2).mpr hb
    exact h
  have hr' : ∀ s ∈ atomIntervalRanges role lo hi 0,
      s.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) :=
    (initialWordPrior_atomIntervals_equiv role (m + 1) nc b.val
      (characterCellSize r f) cell P Q R cellLo cellHi hcell x hx).mpr hr
  have herr := character_word_interval_errors b.val c hc T a
    (characterFillerTarget logX Δ b.val T a)
    (fun v => ∏ i, cellLo ⟨v, i⟩) (fun v => ∏ i, cellHi ⟨v, i⟩) hlo hhi
  have hw := character_initial_product_window k logX Δ b.val c T a lo hi herr.1 herr.2
    (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)) hr'
  change (scheduleAtomTotal role ⟨0, fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)⟩ : ℝ) /
    Real.exp logX ∈ Set.Icc (Real.exp (Δ - C)) (Real.exp (Δ + C)) at hw
  have ht := initial_atom_total role
    (fun v : CharacterRole k => initialWordSize (m + 1) (characterCellSize r f) v.2)
    (fun i => (x i : ℕ))
  rw [ht] at hw
  have hprod : (∏ i, (x i : ℕ)) = ∏ j, (y j : ℕ) := e.prod_comp (fun j => (y j : ℕ))
  simpa only [hprod, Nat.cast_prod] using hw

end Ostmann

end OAI

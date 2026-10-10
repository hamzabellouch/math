import OAI.NumberTheory.Ostmann.Characters.CharacterInitialAmplitude
import OAI.NumberTheory.Ostmann.Characters.CharacterFullPrimeCells
import OAI.NumberTheory.Ostmann.Construction.ScheduledArithmeticIteration

namespace OAI

/-! # Identification with the literal scheduled initial amplitude -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem character_initial_scheduled_amplitude (k m nc : ℕ) (r : Fin k → ℕ) (f : ℕ)
    (cell : (Σ v, Fin (characterCellSize r f v)) ≃ Fin nc)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (cellLo cellHi : (Σ v, Fin (characterCellSize r f v)) → ℕ)
    (hcell : ∀ i q, q ∈ R (cell i) → cellLo i ≤ q ∧ q ≤ cellHi i)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (pivot : ℕ → (Σ v, Fin (characterSize m r f v)))
    (center : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ))
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (logX Δ τ c : ℝ) (hc : 1 ≤ c) (T : Fin k → ℝ) (a : Fin k → Bool → ℝ)
    (V cap : ℕ → ℕ) (b : Fin (⌊4 * τ⌋₊ + 1))
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
    let χ₀ := signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ
    scheduledConstituentAmplitude (characterRole k) (characterSize m r f) χ₀
      (fun i => primeGaussMultiplier (χ₀ i)) pivot P hP
      (characterFullPrimeCells m r f Q (fun v i => R (cell ⟨v, i⟩))) lo hi V cap
      (scheduleFourierLeaf (characterRole k) ψ (Real.exp logX)
        (Real.exp (Δ - C)) (Real.exp (Δ + C))) center 0 =
    wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) χ center ψ (Real.exp logX) (V 0)
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b := by
  have hh := character_initial_amplitude k m nc r f cell P hP Q R cellLo cellHi hcell
    χ hχ pivot center ψ heven logX Δ τ c hc T a (V 0) V cap b hlo hhi hbin
  have hQ : (fun i => Fin.append (Fin.append Q R) (Fin.append Q R)
      (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i)) =
      characterFullPrimeCells m r f Q (fun v i => R (cell ⟨v, i⟩)) := by
    funext i
    have he := characterFullPrimeCells_source m nc r f cell Q
      (fun v j => R (cell ⟨v, j⟩)) i
    simpa only [cell.apply_symm_apply] using he
  have hχ₀ : (fun i : Σ v, Fin (characterSize m r f v) => wordCopyCharacter (m + 1) nc χ
      (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i)) =
      signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ := by
    funext i
    exact initialWordTupleEquiv_character (m + 1) nc (characterCellSize r f) cell χ i
  have hκ : (fun i : Σ v, Fin (characterSize m r f v) => primeGaussMultiplier (wordCopyCharacter (m + 1) nc χ
      (initialWordTupleEquiv (m + 1) nc (characterCellSize r f) cell i))) =
      (fun i => primeGaussMultiplier
        (signedAtomCharacter (initialWordSize (m + 1) (characterCellSize r f)) χ i)) := by
    funext i
    exact congrArg primeGaussMultiplier (congrFun hχ₀ i)
  dsimp only at hh
  dsimp only
  unfold scheduledConstituentAmplitude
  apply Eq.trans ?_ hh
  congr 1
  · exact hχ₀.symm
  · exact hκ.symm
  · exact hQ.symm

end Ostmann

end OAI

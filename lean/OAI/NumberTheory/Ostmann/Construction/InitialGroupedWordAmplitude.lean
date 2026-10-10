import OAI.NumberTheory.Ostmann.Construction.InitialWordBinIdentification
import OAI.NumberTheory.Ostmann.Construction.InitialWordExpectation

namespace OAI

/-! # Exact identification of the grouped initial expectation with the word amplitude -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem initial_grouped_word_expectation {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole) (a m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (a + 1) → Finset ℕ) (R : Fin m → Finset ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X τ : ℝ) (N : ℕ) (b : Fin (⌊4 * τ⌋₊ + 1))
    (hbin : ∀ y : Fin (((a + 1) + m) + ((a + 1) + m)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) ≤ 4 * τ) :
    (∑ x : (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)) → P,
      ((∏ i, primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R)
          (initialWordTupleEquiv (a + 1) m s cell i)) (x i) : ℝ) : ℂ) *
      if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) ∧
          (∀ r ∈ initialWordBinRanges role b.val,
            r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) then
        sampledTupleAmplitude P hP
          (fun i => wordCopyCharacter (a + 1) m χ (initialWordTupleEquiv (a + 1) m s cell i))
          t ψ X N x else 0) =
    wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) χ t ψ X N
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b := by
  refine (initial_prime_expectation_reindex (initialWordTupleEquiv (a + 1) m s cell)
    P hP (Fin.append (Fin.append Q R) (Fin.append Q R))
    (wordCopyCharacter (a + 1) m χ) t ψ X N
    (fun x => ∀ r ∈ initialWordBinRanges role b.val,
      r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ)))).trans ?_
  rw [wordGraphAmplitude_univ, wordCopyPrimePrior]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hz : productPrior (fun i => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · obtain ⟨hp, hn⟩ := hbin y hz
    have hr := initialWordBinRanges_iff_bin role a m s cell P hP τ b y hp hn
    apply congrArg (fun z : ℂ => (productPrior (fun i => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y : ℂ) * z)
    have hg : (Function.Injective y ∧
        ∀ r ∈ initialWordBinRanges role b.val,
          r.Holds (fun v => ∏ i, (y (initialWordTupleEquiv (a + 1) m s cell ⟨v.val, i⟩) : ℕ))) ↔
        (Function.Injective y ∧
          wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) = b ∧
          wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) = b) :=
      and_congr_right (fun _ => hr)
    by_cases h : Function.Injective y ∧
        wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) = b ∧
        wordLogBin τ (fun i => Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) = b
    · have h' := hg.mpr h
      exact (ite_eq_left h').trans (ite_eq_left h).symm
    · have h' : ¬ (Function.Injective y ∧
          ∀ r ∈ initialWordBinRanges role b.val,
            r.Holds (fun v => ∏ i, (y (initialWordTupleEquiv (a + 1) m s cell ⟨v.val, i⟩) : ℕ))) :=
        fun hh => h (hg.mp hh)
      exact (ite_eq_right h').trans (ite_eq_right h).symm

end Ostmann

end OAI

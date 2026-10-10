import OAI.NumberTheory.Ostmann.Construction.InitialScheduleWordAmplitude

namespace OAI

/-! # Prior-supported interval guards preserve the original initial statistic -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem initial_schedule_word_amplitude_of_range_equiv {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole) (a m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (a + 1) → Finset ℕ) (R : Fin m → Finset ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (pivot : ℕ → (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)))
    (center : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X τ lo hi : ℝ) (hX : 0 < X)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v) (N : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (b : Fin (⌊4 * τ⌋₊ + 1))
    (hranges : ∀ x : (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)) → P,
      (∏ i, primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R)
          (initialWordTupleEquiv (a + 1) m s cell i)) (x i)) ≠ 0 →
      ((∀ r ∈ ranges 0, r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) ↔
        ∀ r ∈ initialWordBinRanges role b.val,
          r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))))
    (hbin : ∀ y : Fin (((a + 1) + m) + ((a + 1) + m)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) ≤ 4 * τ)
    (hwindow : ∀ x : (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)) → P,
      (∏ i, primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R)
          (initialWordTupleEquiv (a + 1) m s cell i)) (x i)) ≠ 0 →
      (∀ r ∈ ranges 0, r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) →
      ((∏ i, (x i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi) :
    constituentPrimeGuardedAmplitude role (fun v => initialWordSize (a + 1) s v.2)
      (fun i => wordCopyCharacter (a + 1) m χ (initialWordTupleEquiv (a + 1) m s cell i))
      (fun i => primeGaussMultiplier
        (wordCopyCharacter (a + 1) m χ (initialWordTupleEquiv (a + 1) m s cell i)))
      pivot 0 P hP
      (fun i => Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv (a + 1) m s cell i))
      childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      (fun v : Finset.Icc (-(N : ℤ)) (N : ℤ) => (v : ℤ)) center =
    wordGraphAmplitude P hP (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) χ center ψ X N
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b := by
  let : Nonempty (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)) :=
    ⟨⟨(true, none), ⟨0, Nat.succ_pos a⟩⟩⟩
  have ht := initial_guarded_expectation role (fun v => initialWordSize (a + 1) s v.2)
    (fun i => wordCopyCharacter (a + 1) m χ (initialWordTupleEquiv (a + 1) m s cell i))
    P hP (fun i => Fin.append (Fin.append Q R) (Fin.append Q R)
      (initialWordTupleEquiv (a + 1) m s cell i))
    (fun i p hp => wordCopyCharacter_ne_one χ p (hχ p hp) _)
    pivot center ψ X lo hi hX heven N childBound pivotBound ranges hwindow
  have hu := initial_grouped_word_expectation role a m s cell P hP Q R χ center
    ψ X τ N b hbin
  refine ht.trans (Eq.trans ?_ hu)
  rw [finite_enumeration_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hz : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv (a + 1) m s cell i)) (x i)) = 0
  · simp only [hz, Complex.ofReal_zero, zero_mul]
  · simp only [hranges x hz]

end Ostmann

end OAI

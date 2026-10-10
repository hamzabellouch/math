import OAI.NumberTheory.Ostmann.Construction.InitialScheduleWordAmplitude

namespace OAI

/-! # Original-prior support supplies the initial bin and product windows -/

namespace Ostmann
open scoped Classical BigOperators

theorem word_copy_log_upper {A : Type*} [Fintype A] {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ) (f : A → ℝ) (T : ℝ)
    (hword : ∀ w, productPrior μ w ≠ 0 → (∑ i, f (w i)) ≤ T)
    (y : Fin ((k + m) + (k + m)) → A)
    (hy : productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) y ≠ 0) :
    (∑ i, f (((wordCopyEquiv A k m).symm y).1.1 i)) ≤ T ∧
      (∑ i, f (((wordCopyEquiv A k m).symm y).2.1 i)) ≤ T := by
  let z := (wordCopyEquiv A k m).symm y
  have he : wordCopyEquiv A k m z = y := Equiv.apply_symm_apply _ _
  rw [← he, wordCopyPrior] at hy
  exact ⟨hword _ (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).1).1,
    hword _ (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).2).1⟩

theorem prime_word_log_upper (P : Finset ℕ) {k : ℕ}
    (Q : Fin k → Finset ℕ) (U : Fin k → ℝ) (T : ℝ)
    (hU : ∀ i p, p ∈ Q i → Real.log (p : ℝ) ≤ U i) (hT : (∑ i, U i) ≤ T)
    (w : Fin k → P) (hw : productPrior (fun i => primeSubsetPrior P (Q i)) w ≠ 0) :
    (∑ i, Real.log (w i : ℝ)) ≤ T := by
  apply (Finset.sum_le_sum (fun i _ => hU i _ ?_)).trans hT
  exact primeSubsetPrior_support P (Q i) (w i)
    ((Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i))

theorem initial_grouped_word_window {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole) (a m : ℕ) (s : C → ℕ)
    (cell : (Σ c, Fin (s c)) ≃ Fin m) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin (a + 1) → Finset ℕ) (R : Fin m → Finset ℕ)
    (X τ lo hi : ℝ) (b : Fin (⌊4 * τ⌋₊ + 1))
    (hbin : ∀ y : Fin (((a + 1) + m) + ((a + 1) + m)) → P,
      productPrior (fun i => primeSubsetPrior P
        (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 →
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
      (∑ i, Real.log (((wordCopyEquiv P (a + 1) m).symm y).2.1 i : ℝ)) ≤ 4 * τ)
    (hwin : ∀ y ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b,
      ((∏ i, (y i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi)
    (x : (Σ v : Bool × Option C, Fin (initialWordSize (a + 1) s v.2)) → P)
    (hx : (∏ i, primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R)
        (initialWordTupleEquiv (a + 1) m s cell i)) (x i)) ≠ 0)
    (hr : ∀ r ∈ initialWordBinRanges role b.val,
      r.Holds (fun v => ∏ i, (x ⟨v.val, i⟩ : ℕ))) :
    ((∏ i, (x i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi := by
  let e := initialWordTupleEquiv (a + 1) m s cell
  let y := fun j => x (e.symm j)
  have hp : productPrior (fun i => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0 := by
    intro hz
    exact hx ((prime_prior_reindex e P (Fin.append (Fin.append Q R) (Fin.append Q R)) x).trans hz)
  obtain ⟨hpos, hneg⟩ := hbin y hp
  have hr' : ∀ r ∈ initialWordBinRanges role b.val,
      r.Holds (fun v => ∏ i, (y (e ⟨v.val, i⟩) : ℕ)) := by
    simpa only [y, e.symm_apply_apply] using hr
  have hb := (initialWordBinRanges_iff_bin role a m s cell P hP τ b y hpos hneg).mp hr'
  have hy : y ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) b := by
    apply (mem_wordCharacterEvent _ _ _ _ y).mpr
    refine ⟨hb, ?_⟩
    rwa [wordCopyPrimePrior]
  have hprod : (∏ i, (x i : ℕ)) = ∏ j, (y j : ℕ) :=
    prime_product_reindex e P x
  rw [hprod]
  exact hwin y hy

end Ostmann

end OAI

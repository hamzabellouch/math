import OAI.NumberTheory.Ostmann.Construction.WordCharacterStatistic
import OAI.NumberTheory.Ostmann.Construction.HarmonicRepeatRemoval

namespace OAI

/-! # Repeat removal for the actual two-copy word statistic -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def wordCharacterEvent {A B : Type*} [Fintype A] {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ) (bin : (Fin k → A) → B) (b : B) :
    Finset (Fin ((k + m) + (k + m)) → A) :=
  Finset.univ.filter (fun x =>
    (bin ((wordCopyEquiv A k m).symm x).1.1 = b ∧
      bin ((wordCopyEquiv A k m).symm x).2.1 = b) ∧
    productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x ≠ 0)

theorem wordCharacterMean_eq_event_sum {A B : Type*} [Fintype A] {k m : ℕ}
    (v : A → ℕ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (bin : (Fin k → A) → B) (b : B) :
    wordCharacterMean v μ ν χ t ψ X bin b =
      ∑ x ∈ wordCharacterEvent μ ν bin b,
        (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
          characterTupleSum (v ∘ x) (wordCopyCharacter k m χ) t ψ X := by
  unfold wordCharacterMean wordCharacterEvent
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hb : bin ((wordCopyEquiv A k m).symm x).1.1 = b ∧
      bin ((wordCopyEquiv A k m).symm x).2.1 = b
  · by_cases hw : productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x = 0
    · simp [hw]
    · simp [hb, hw]
  · simp [hb]

noncomputable def injectiveWordCharacterMean {A B : Type*} [Fintype A] {k m : ℕ}
    (v : A → ℕ) (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (bin : (Fin k → A) → B) (b : B) : ℂ :=
  ∑ x ∈ (wordCharacterEvent μ ν bin b).filter Function.Injective,
    (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
      characterTupleSum (v ∘ x) (wordCopyCharacter k m χ) t ψ X

theorem wordCopyPrimePrior {k m : ℕ} (P : Finset ℕ)
    (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ) :
    Fin.append (Fin.append (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)))
      (Fin.append (fun i => primeSubsetPrior P (Q i)) (fun j => primeSubsetPrior P (R j))) =
      fun i => primeSubsetPrior P (Fin.append (Fin.append Q R) (Fin.append Q R) i) := by
  have h₁ := map_fin_append (primeSubsetPrior P) Q R
  have h₂ := map_fin_append (primeSubsetPrior P) (Fin.append Q R) (Fin.append Q R)
  rw [← h₁] at h₂
  exact h₂

theorem word_character_repeat_removal {B : Type*} {k m : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X H U D : ℝ)
    (hX : 0 < X) (hU : 0 < U)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (hsmall : ∀ p ∈ P, H * U < p)
    (bin : (Fin k → P) → B) (b : B)
    (hupper : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, (∏ i, (x i : ℝ)) ≤ X * U)
    (hlower : ∀ x ∈ wordCharacterEvent (fun i => primeSubsetPrior P (Q i))
      (fun j => primeSubsetPrior P (R j)) bin b, X * Real.exp D ≤ ∏ i, (x i : ℝ)) :
    let μ := fun i => primeSubsetPrior P (Q i)
    let ν := fun j => primeSubsetPrior P (R j)
    ‖wordCharacterMean Subtype.val μ ν χ t ψ X bin b -
      injectiveWordCharacterMean Subtype.val μ ν χ t ψ X bin b‖ ≤
      Real.sqrt X * (‖𝓕 ψ 0‖ *
        (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) *
        (((k + m) + (k + m) : ℕ) : ℝ) ^ ((k + m) + (k + m)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2)) := by
  intro μ ν
  rw [wordCharacterMean_eq_event_sum]
  unfold injectiveWordCharacterMean
  rw [wordCopyPrimePrior]
  have hr := harmonic_repeat_removal P hP _ (Fin.append (Fin.append Q R) (Fin.append Q R))
    (wordCharacterEvent μ ν bin b) (wordCopyCharacter k m χ)
    (fun i p hp => wordCopyCharacter_ne_one χ p (hχ p hp) i)
    t ψ X H U D hX hU hsupp hsmall hupper hlower
  convert hr using 1
  congr 2
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter]
  · intro x _
    rfl

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Construction.InitialAmplitudeReindex
import OAI.NumberTheory.Ostmann.Construction.WordGraphAmplitude

namespace OAI

/-! # The ordered word amplitude as an unchanged-prior guarded expectation -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem prime_prior_reindex {I : Type*} [Fintype I] {n : ℕ}
    (e : I ≃ Fin n) (P : Finset ℕ) (Q : Fin n → Finset ℕ) (x : I → P) :
    (∏ i, primeSubsetPrior P (Q (e i)) (x i)) =
      productPrior (fun j => primeSubsetPrior P (Q j)) (fun j => x (e.symm j)) := by
  unfold productPrior
  have h := Equiv.prod_comp e.symm (fun i => primeSubsetPrior P (Q (e i)) (x i))
  simpa only [e.apply_symm_apply] using h.symm

theorem prime_product_reindex {I : Type*} [Fintype I] {n : ℕ}
    (e : I ≃ Fin n) (P : Finset ℕ) (x : I → P) :
    (∏ i, (x i : ℕ)) = ∏ j, (x (e.symm j) : ℕ) :=
  (Equiv.prod_comp e.symm (fun i => (x i : ℕ))).symm

theorem mem_wordCharacterEvent {A B : Type*} [Fintype A] {k m : ℕ}
    (μ : Fin k → A → ℝ) (ν : Fin m → A → ℝ) (bin : (Fin k → A) → B) (b : B)
    (x : Fin ((k + m) + (k + m)) → A) :
    x ∈ wordCharacterEvent μ ν bin b ↔
      (bin ((wordCopyEquiv A k m).symm x).1.1 = b ∧
        bin ((wordCopyEquiv A k m).symm x).2.1 = b) ∧
      productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x ≠ 0 := by
  simp only [wordCharacterEvent, Finset.mem_filter, Finset.mem_univ, true_and]

theorem wordGraphAmplitude_univ {B : Type*} {k m : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (μ : Fin k → P → ℝ) (ν : Fin m → P → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (bin : (Fin k → P) → B) (b : B) :
    wordGraphAmplitude P hP μ ν χ t ψ X N bin b =
      ∑ x : Fin ((k + m) + (k + m)) → P,
        (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
          if Function.Injective x ∧
              bin ((wordCopyEquiv P k m).symm x).1.1 = b ∧
              bin ((wordCopyEquiv P k m).symm x).2.1 = b then
            sampledTupleAmplitude P hP (wordCopyCharacter k m χ) t ψ X N x else 0 := by
  unfold wordGraphAmplitude wordCharacterEvent
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x = 0
  · simp only [hp, Complex.ofReal_zero, zero_mul, ite_self]
  · by_cases hi : Function.Injective x <;>
      by_cases hb₁ : bin ((wordCopyEquiv P k m).symm x).1.1 = b <;>
      by_cases hb₂ : bin ((wordCopyEquiv P k m).symm x).2.1 = b <;>
      simp [ne_eq, hp, hi, hb₁, hb₂]

/-- Reindexing changes no original marginal and no prime-pairwise test. -/
theorem initial_prime_expectation_reindex {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (e : I ≃ Fin n) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : Fin n → Finset ℕ) (χ : Fin n → ∀ p : ℕ, DirichletCharacter ℂ p)
    (t : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ)
    (R : (I → P) → Prop) [DecidablePred R] :
    (∑ x : I → P, ((∏ i, primeSubsetPrior P (Q (e i)) (x i) : ℝ) : ℂ) *
      if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) ∧
          R x then
        sampledTupleAmplitude P hP (fun i => χ (e i)) t ψ X N x else 0) =
    ∑ x : Fin n → P, (productPrior (fun j => primeSubsetPrior P (Q j)) x : ℂ) *
      if Function.Injective x ∧ R (fun i => x (e i)) then
        sampledTupleAmplitude P hP χ t ψ X N x else 0 := by
  let f : (Fin n → P) ≃ (I → P) := Equiv.arrowCongr e.symm (Equiv.refl P)
  rw [← f.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  have hp : (∏ i, primeSubsetPrior P (Q (e i)) (x (e i))) =
      productPrior (fun j => primeSubsetPrior P (Q j)) x :=
    Equiv.prod_comp e (fun j => primeSubsetPrior P (Q j) (x j))
  have hi : Pairwise (fun i j => (x (e i) : ℕ).Coprime (x (e j) : ℕ)) ↔
      Function.Injective x := by
    rw [prime_sample_pairwise_iff_injective P hP]
    exact ⟨fun h i j hij => by
      have hh := h (show x (e (e.symm i)) = x (e (e.symm j)) by simpa using hij)
      simpa using congrArg e hh,
      fun h i j hij => e.injective (h hij)⟩
  change ((∏ i, primeSubsetPrior P (Q (e i)) (x (e i)) : ℝ) : ℂ) *
    (if Pairwise (fun i j => (x (e i) : ℕ).Coprime (x (e j) : ℕ)) ∧
      R (fun i => x (e i)) then
      sampledTupleAmplitude P hP (fun i => χ (e i)) t ψ X N (fun i => x (e i)) else 0) = _
  rw [hp, hi, sampledTupleAmplitude_equiv]
  by_cases h : Function.Injective x ∧ R (fun i => x (e i))
  · simp only [h]
  · simp only [h, ite_false]

end Ostmann

end OAI

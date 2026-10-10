import OAI.NumberTheory.Ostmann.Construction.ConstituentDiagonal
import OAI.NumberTheory.Ostmann.Construction.ConstituentFrequencySupport
import OAI.NumberTheory.Ostmann.Construction.PrimeDiagonalMatching

namespace OAI

/-! # Prime matching for the actual original-prior diagonal -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

section

variable {I D : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
variable (center : ∀ p : ℕ, ZMod p)
variable (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)

theorem constituentRetainedCoefficient_weight_ne_zero
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ≠ 0) :
    constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0 := by
  unfold constituentRetainedCoefficient at ha
  exact (mul_ne_zero_iff.mp ha).1

include hP in
theorem constituentTransferWeight_prime_injective
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    Function.Injective (fun h => (a.1 h : ℕ)) := by
  unfold constituentTransferWeight at ha
  split_ifs at ha with hg
  · intro h k he
    dsimp only at he
    by_contra hne
    have hc := hg (show Sum.inl h ≠ Sum.inl k from fun hh => hne (Sum.inl.inj hh))
    change (a.1 h : ℕ).Coprime (a.1 k : ℕ) at hc
    rw [he] at hc
    exact (hP _ (a.1 k).property).ne_one (by simpa only [Nat.coprime_self] using hc)
  · exact False.elim (ha rfl)

theorem constituentRetainedCoefficient_prime_injective
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ≠ 0) :
    Function.Injective (fun h => (a.1 h : ℕ)) := by
  exact constituentTransferWeight_prime_injective role size n P hP Q childBound pivotBound ranges
    leaf hist u M a (constituentRetainedCoefficient_weight_ne_zero role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ha)

theorem constituentRetainedCoefficient_root_ne_zero
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ≠ 0) :
    frequencyRoot n (hist a.2) ≠ 0 := by
  have hw := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound ranges
    leaf hist u M a (constituentRetainedCoefficient_weight_ne_zero role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M a ha)
  exact fullAtomTransferWeight_all_frequencies_ne_zero role childBound pivotBound ranges leaf hzero
    n _ (hist a.2) hw _ (frequencyRoot_mem_allFrequencyList n (hist a.2))

theorem constituentPivotDiagonal_permutations [Fintype D]
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d p, p ∈ P → (frequencyRoot n (hist d)).natAbs < p) :
    constituentPivotDiagonal role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center u M =
      primePermutationCorrelation P (fun d => frequencyRoot n (hist d))
        (constituentRetainedCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist center u M) := by
  unfold constituentPivotDiagonal
  have ht := @prime_pivotDiagonal_eq_correlation
    (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n) D inferInstance inferInstance
    P hP (fun d => frequencyRoot n (hist d))
    (constituentRetainedCoefficient role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M)
    (constituentRetainedCoefficient_prime_injective role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M)
    (constituentRetainedCoefficient_root_ne_zero role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M hzero)
    (fun a _ h => hsmall a.2 _ (a.1 h).property)
  convert ht using 1
  with_reducible exact pivotDiagonal_fintype_eq _ _ _ _ _

end

end Ostmann

end OAI

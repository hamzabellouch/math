import OAI.NumberTheory.Ostmann.Construction.ConstituentDiagonalMatching
import OAI.NumberTheory.Ostmann.Construction.RetainedAdditiveMatching

namespace OAI

/-! # Removing the common additive factor from the actual diagonal -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def constituentCharacterCoefficient {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  letI : ∀ h, Fact (a.1 h : ℕ).Prime := fun h => ⟨hP _ (a.1 h).property⟩
  letI : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  exact constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a *
    retainedCharacterBranch (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ))
      (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
      (scheduledRetainedGraph ρ initialCompleteGraph pivot n)
      (fun h => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) h.val (a.1 h))
      (fun y => copyScheduleUnary χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        n (hist a.2) y.val (u y)) M

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

theorem constituentRetainedCoefficient_matching
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d d' : D)
    (hv : frequencyRoot n (hist d) = frequencyRoot n (hist d')) :
    constituentRetainedCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist center u M (l, d) *
      conj (constituentRetainedCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist center u M (l ∘ e.symm, d')) =
    constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) := by
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ h, Fact ((l ∘ e.symm) h : ℕ).Prime := fun h => ⟨hP _ ((l ∘ e.symm) h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  unfold constituentRetainedCoefficient constituentCharacterCoefficient
  dsimp only
  rw [← hv]
  exact retainedPrimePhase_matching (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
    e.symm center _ _ _ _ _ _ _ _ _ _ M _ _ _

theorem constituentPivotDiagonal_characters [Fintype D]
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (hsmall : ∀ d p, p ∈ P → (frequencyRoot n (hist d)).natAbs < p) :
    constituentPivotDiagonal role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist center u M =
      primePermutationCorrelation P (fun d => frequencyRoot n (hist d))
        (constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M) := by
  apply Eq.trans (constituentPivotDiagonal_permutations role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist center u M hzero hsmall)
  exact primePermutationCorrelation_congr P (fun d => frequencyRoot n (hist d)) _ _
    (constituentRetainedCoefficient_matching role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center u M)

end

end Ostmann

end OAI

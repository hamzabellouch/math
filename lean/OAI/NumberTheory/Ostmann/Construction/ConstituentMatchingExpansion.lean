import Mathlib.Logic.Equiv.Prod
import OAI.NumberTheory.Ostmann.Construction.ConstituentDiagonalSupport

namespace OAI

/-! # The literal matching sum under its original H and Y priors -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sum_split_prime_prior {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (F : (H ⊕ Y → P) → ℂ) :
    (∑ x : H ⊕ Y → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * F x) =
      ∑ u : Y → P, ((∏ y, primeSubsetPrior P (Q (.inr y)) (u y) : ℝ) : ℂ) *
        ∑ l : H → P, ((∏ h, primeSubsetPrior P (Q (.inl h)) (l h) : ℝ) : ℂ) *
          F (Sum.elim l u) := by
  rw [← (Equiv.sumArrowEquivProdArrow H Y P).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Fintype.prod_sum_type, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Complex.ofReal_mul]
  change _ * F (Sum.elim l u) = _
  ring

section
variable {I D : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

/-- The pair is integrated before the external-pivot sum. The second H prior
is kept explicitly, with the inverse of the matching in the diagonal. -/
noncomputable def constituentOriginalMatchedPair
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (d d' : D) (M : ℕ) : ℂ :=
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let Qr : CopyScheduleH ρ n ⊕ CopyScheduleY ρ n → Finset ℕ := Sum.elim
    (fun h => Q (copyScheduleOrigin n h.val)) (fun y => Q (copyScheduleOrigin n y.val))
  let core := fun x : CopyScheduleH ρ n ⊕ CopyScheduleY ρ n → P =>
    constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist
      (fun y => x (.inr y)) M
  ∑ x, ((∏ i, primeSubsetPrior P (Qr i) (x i) : ℝ) : ℂ) *
    ((∏ h, primeSubsetPrior P (Qr (.inl h)) (x (.inl (e.symm h))) : ℝ) : ℂ) *
    (core x ((fun h => x (.inl h)), d) * conj (core x ((fun h => x (.inl (e.symm h))), d')))

omit [Fintype D] in
theorem constituentOriginalMatchedPair_eq
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (d d' : D) (M : ℕ) :
    constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist e d d' M =
      ∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
        ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
        ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
          constituentCharacterCoefficient role size χ κ pivot n P hP Q childBound pivotBound ranges
            leaf hist u M (l, d) *
          conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q childBound pivotBound ranges
            leaf hist u M (l ∘ e.symm, d')) := by
  unfold constituentOriginalMatchedPair
  simp_rw [mul_assoc]
  have hsplit := sum_split_prime_prior (H := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)
    (Y := CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n) P
    (Sum.elim (fun h => Q (copyScheduleOrigin n h.val)) (fun y => Q (copyScheduleOrigin n y.val)))
    (fun x => ((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val))
      (x (.inl (e.symm h))) : ℝ) : ℂ) *
      (constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist
        (fun y => x (.inr y)) M ((fun h => x (.inl h)), d) *
      conj (constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist
        (fun y => x (.inr y)) M ((fun h => x (.inl (e.symm h))), d'))))
  simp only [finite_univ_canonical, Sum.elim_inl, Sum.elim_inr] at hsplit ⊢
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [constituentCharacterCoefficient_factor, constituentCharacterCoefficient_factor]
  simp only [Function.comp_apply, map_mul, Complex.conj_ofReal, finite_univ_canonical]
  dsimp only [Function.comp_def]
  ring

theorem constituentMatchingFamily_expand
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))) (M : ℕ) :
    constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist S M =
      ∑ e ∈ S, ∑ d : D, ∑ d' : D, if frequencyRoot n (hist d) = frequencyRoot n (hist d') then
        constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist e d d' M
        else 0 := by
  simp_rw [constituentOriginalMatchedPair_eq]
  unfold constituentMatchingFamily primeMatchingContribution
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d' _
  by_cases h : frequencyRoot n (hist d) = frequencyRoot n (hist d')
  · simp only [h, ite_true, Finset.mul_sum, finite_univ_canonical]
  · simp only [h, ite_false, mul_zero, Finset.sum_const_zero]

end
end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchingExpansion
import OAI.NumberTheory.Ostmann.Construction.DiagonalEndpointCancellation

namespace OAI

/-! # Summing matched prime comparisons before counting external pivots -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {I D : Type*} [Fintype I] [Fintype D]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (Q : (Σ i, Fin (size i)) → Finset ℕ)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)

theorem constituentMatchingFamily_pair_sum_bound
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (M : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ e ∈ S, ∀ d d', frequencyRoot n (hist d) = frequencyRoot n (hist d') →
      ‖constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges
        leaf hist e d d' M‖ ≤ E) :
    ‖constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist S M‖ ≤
      (S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 * E := by
  rw [constituentMatchingFamily_expand]
  calc
    _ ≤ ∑ e ∈ S, ‖∑ d : D, ∑ d' : D, if frequencyRoot n (hist d) = frequencyRoot n (hist d') then
        constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges
          leaf hist e d d' M else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ S, (Fintype.card D : ℝ) ^ 2 * E := by
      apply Finset.sum_le_sum
      intro e he
      calc
        _ ≤ ∑ d : D, ∑ d' : D, ‖if frequencyRoot n (hist d) = frequencyRoot n (hist d') then
            constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges
              leaf hist e d d' M else 0‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => norm_sum_le _ _)
        _ ≤ ∑ _d : D, ∑ _d' : D, E := by
          apply Finset.sum_le_sum
          intro d _
          apply Finset.sum_le_sum
          intro d' _
          split_ifs with hr
          · exact hpair e he d d' hr
          · simpa only [norm_zero] using hE
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem constituentMatchingFamily_interval_pair_bound
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (a b : ℕ) (ha : 0 < a) (gap E : ℝ) (hE : 0 ≤ E)
    (loH : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℝ)
    (hloH : ∀ h, 0 < loH h) (hgap : Real.exp gap * (b : ℝ) ≤ ∏ h, loH h)
    (hpair : ∀ M ∈ Finset.Icc a b, ∀ e ∈ S, ∀ d d',
      frequencyRoot n (hist d) = frequencyRoot n (hist d') →
      ‖constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges
        leaf hist e d d' M‖ ≤
        (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * (∏ h, loH h)⁻¹ * E) :
    (∑ M ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist S M).re) ≤
      Real.exp (-gap) * ((S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 *
        (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹)) * E := by
  let Z : ℝ := ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
    (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹
  have hZ : 0 ≤ Z := Finset.prod_nonneg fun _ _ => by positivity
  have hlo : 0 ≤ (∏ h, loH h)⁻¹ := inv_nonneg.mpr
    (Finset.prod_nonneg fun h _ => (hloH h).le)
  apply finite_pivot_sum_bound a b ha _ ((S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 * Z)
    E gap (by positivity) hE _ loH hloH hgap
  intro M hM
  calc
    _ ≤ (S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 * (Z * (∏ h, loH h)⁻¹ * E) :=
      constituentMatchingFamily_pair_sum_bound role size χ κ pivot n P hP Q childBound pivotBound
        ranges leaf hist S M _ (mul_nonneg (mul_nonneg hZ hlo) hE) (hpair M hM)
    _ = _ := by ring

end
end Ostmann

end OAI

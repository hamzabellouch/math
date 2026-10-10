import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchingPairSum
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

theorem constituentMatchingFamily_interval_pair_product
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (a b : ℕ) (ha : 0 < a) (gap E : ℝ) (hE : 0 ≤ E)
    (productLower : ℝ) (hpositive : 0 < productLower)
    (hgap : Real.exp gap * (b : ℝ) ≤ productLower)
    (hpair : ∀ M ∈ Finset.Icc a b, ∀ e ∈ S, ∀ d d',
      frequencyRoot n (hist d) = frequencyRoot n (hist d') →
      ‖constituentOriginalMatchedPair role size χ κ pivot n P hP Q childBound pivotBound ranges
        leaf hist e d d' M‖ ≤
        (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * productLower⁻¹ * E) :
    (∑ M ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges leaf hist S M).re) ≤
      Real.exp (-gap) * ((S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 *
        (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹)) * E := by
  let Z : ℝ := ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
    (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹
  have hZ : 0 ≤ Z := Finset.prod_nonneg fun _ _ => by positivity
  have hlo : 0 ≤ productLower⁻¹ := inv_nonneg.mpr hpositive.le
  apply finite_pivot_sum_bound a b ha _ ((S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 * Z)
    E gap (by positivity) hE Unit (fun _ => productLower) (fun _ => hpositive) (by simpa using hgap)
  intro M hM
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_unit, pow_one]
  calc
    _ ≤ (S.card : ℝ) * (Fintype.card D : ℝ) ^ 2 * (Z * productLower⁻¹ * E) :=
      constituentMatchingFamily_pair_sum_bound role size χ κ pivot n P hP Q childBound pivotBound
        ranges leaf hist S M _ (mul_nonneg (mul_nonneg hZ hlo) hE) (hpair M hM)
    _ = _ := by ring

end
end Ostmann

end OAI

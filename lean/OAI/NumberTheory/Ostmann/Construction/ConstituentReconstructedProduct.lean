import OAI.NumberTheory.Ostmann.Construction.ConstituentGuardedProduct
import OAI.NumberTheory.Ostmann.Construction.ConstituentNextSupport

namespace OAI

/-! # Exact coefficient reconstruction with the original integer-pivot tests -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem constituentTransferWeight_reconstructed_product {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (K V : ℕ) (T : Finset ℕ)
    (hTpos : ∀ M ∈ T, 0 < M) (hTbound : ∀ M ∈ T, M ≤ pivotBound n)
    (hTfull : ∀ M, 0 < M → M ≤ pivotBound n →
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) t ≠ 0 → M ∈ T)
    (hcutL : ∀ M ∈ T,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      (frequencyRoot n t).natAbs ≤ childBound n ∧ (∏ h, (l h : ℕ)) ≤ K)
    (hcutR : ∀ M ∈ T,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      (frequencyRoot n t').natAbs ≤ childBound n ∧ (∏ h, (r h : ℕ)) ≤ K)
    (hscale : ∀ M ∈ T, 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : ∀ M ∈ T,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (r h : ℕ))
    (hrange : ∀ M ∈ T,
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      ∀ a ∈ ranges (n + 1), a.Holds (copiedConstituentAtomValues role size n P u l r)) :
    let N := frequencyRoot n t * (∏ h, (r h : ℕ)) - frequencyRoot n t' * (∏ h, (l h : ℕ))
    let M := reconstructedPivot N s
    (if validTransferredPivot T N s then
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) *
        conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t'))
      else 0) =
    (((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
       (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h)) : ℝ) : ℂ) *
      (if Pairwise (fun i j =>
        ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r j : P) : ℕ)) then
        fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
          (copiedConstituentAtomValues role size n P u l r) (s, t, t') else 0) := by
  dsimp only
  by_cases hvalid : validTransferredPivot T
      (frequencyRoot n t * (∏ h, (r h : ℕ)) - frequencyRoot n t' * (∏ h, (l h : ℕ))) s
  · rw [ite_eq_left hvalid]
    exact constituentTransferWeight_product_guarded role size n p hp P hP Q
      childBound pivotBound ranges leaf u l r s t t' _ K V hvalid.1
      (hTpos _ hvalid.2.2.2) (hTbound _ hvalid.2.2.2)
      (validTransferredPivot_equation T _ s hvalid)
      (hcutL _ hvalid.2.2.2) (hcutR _ hvalid.2.2.2)
      (hscale _ hvalid.2.2.2) hlarge (hgap _ hvalid.2.2.2) (hrange _ hvalid.2.2.2)
  · rw [ite_eq_right hvalid]
    have hz : fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
        (copiedConstituentAtomValues role size n P u l r) (s, t, t') = 0 := by
      by_contra hn
      exact hvalid (fullAtomTransferWeight_copied_validPivot role size n P childBound pivotBound ranges leaf
        u l r s t t' T hTfull hn)
    simp only [hz, ite_self, mul_zero]

end Ostmann

end OAI

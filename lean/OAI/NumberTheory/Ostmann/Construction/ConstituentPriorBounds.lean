import OAI.NumberTheory.Ostmann.Construction.ConstituentFrequencySupport
import OAI.NumberTheory.Ostmann.Construction.SupportedPivotTuples

namespace OAI

/-! # Role-specific product bounds from the original harmonic support -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentTransferWeight_prior_support {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    ∀ h, (a.1 h : ℕ) ∈ Q (copyScheduleOrigin n h.val) := by
  unfold constituentTransferWeight at hw
  split_ifs at hw
  · have hp := (mul_ne_zero_iff.mp hw).1
    have hp' : (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (a.1 h)) ≠ 0 := by
      intro hz
      exact hp (by simp only [hz, Complex.ofReal_zero])
    intro h
    exact primeSubsetPrior_support P _ (a.1 h) ((Finset.prod_ne_zero_iff.mp hp') h (Finset.mem_univ h))
  · exact False.elim (hw rfl)

theorem constituentTransferWeight_product_bounds {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0)
    (lo hi : (Σ i, Fin (size i)) → ℕ)
    (hcell : ∀ i q, q ∈ Q i → lo i ≤ q ∧ q ≤ hi i) :
    (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n, lo (copyScheduleOrigin n h.val)) ≤
      (∏ h, (a.1 h : ℕ)) ∧
    (∏ h, (a.1 h : ℕ)) ≤
      ∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n, hi (copyScheduleOrigin n h.val) := by
  have hp := constituentTransferWeight_prior_support role size n P Q childBound pivotBound ranges leaf hist u M a hw
  exact ⟨Finset.prod_le_prod (fun h _ => (hcell _ _ (hp h)).1),
    Finset.prod_le_prod (fun h _ => (hcell _ _ (hp h)).2)⟩

theorem supportedPivotTuples_product_bounds (P : Finset ℕ) {r : ℕ}
    (Q : Fin r → Finset ℕ) (lo hi : Fin r → ℕ)
    (hcell : ∀ i q, q ∈ Q i → lo i ≤ q ∧ q ≤ hi i)
    (x : Fin r → P) (hx : x ∈ supportedPivotTuples P Q) :
    (∏ i, lo i) ≤ (∏ i, (x i : ℕ)) ∧ (∏ i, (x i : ℕ)) ≤ ∏ i, hi i := by
  have hc := (mem_supportedPivotTuples P Q x).mp hx
  exact ⟨Finset.prod_le_prod (fun i _ => (hcell _ _ (hc.2 i)).1),
    Finset.prod_le_prod (fun i _ => (hcell _ _ (hc.2 i)).2)⟩

end Ostmann

end OAI

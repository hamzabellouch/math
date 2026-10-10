import OAI.NumberTheory.Ostmann.Construction.ConstituentCopiedSupport
import OAI.NumberTheory.Ostmann.Construction.FullWeightForcedNode

namespace OAI

/-! # Exact guarded coefficient multiplication, including zero support -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem constituentTransferWeight_product_guarded {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (l r : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (s : ℤ) (t t' : FrequencyTree ℤ n) (M K V : ℕ)
    (hs : s ≠ 0) (hMpos : 0 < M) (hMbound : M ≤ pivotBound n)
    (hrel : frequencyRoot n t * (∏ h, (r h : ℕ)) -
      frequencyRoot n t' * (∏ h, (l h : ℕ)) = s * M)
    (hcutL : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      (frequencyRoot n t).natAbs ≤ childBound n ∧ (∏ h, (l h : ℕ)) ≤ K)
    (hcutR : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      (frequencyRoot n t').natAbs ≤ childBound n ∧ (∏ h, (r h : ℕ)) ≤ K)
    (hscale : 2 * childBound n * K ≤ V * M)
    (hlarge : ∀ q ∈ P, V < q)
    (hgap : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      2 * pivotBound n * childBound n < ∏ h, (r h : ℕ))
    (hrange : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) ≠ 0 →
      constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 →
      ∀ a ∈ ranges (n + 1), a.Holds (copiedConstituentAtomValues role size n P u l r)) :
    constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) *
      conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t')) =
    (((∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
       (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (r h)) : ℝ) : ℂ) *
      (if Pairwise (fun i j =>
        ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment (fun i : Σ a, Fin (size a) => role i.1) n u l r j : P) : ℕ)) then
        fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
          (copiedConstituentAtomValues role size n P u l r) (s, t, t') else 0) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  have hbranches (hq : Pairwise (fun i j =>
      ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ).Coprime
        ((scheduledCopiedAssignment ρ n u l r j : P) : ℕ))) :
      Pairwise (fun i j => (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j)) ∧
      Pairwise (fun i j => (Sum.elim (fun h => (r h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (r h : ℕ)) (fun y => (u y : ℕ)) j)) := by
    have hm := scheduledCopiedAssignment_map ρ n (fun q : P => (q : ℕ)) u l r
    change Pairwise (fun i j =>
      ((fun i => ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ)) i).Coprime
        ((fun i => ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ)) j)) at hq
    rw [hm] at hq
    exact ⟨scheduledCopiedAssignment_pairwise_branch ρ n _ _ _ hq true,
      scheduledCopiedAssignment_pairwise_branch ρ n _ _ _ hq false⟩
  by_cases hprod : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (l, t) *
      conj (constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t')) = 0
  · by_cases hq : Pairwise (fun i j =>
        ((scheduledCopiedAssignment ρ n u l r i : P) : ℕ).Coprime
          ((scheduledCopiedAssignment ρ n u l r j : P) : ℕ))
    · rw [ite_eq_left hq]
      by_cases hw : fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
          (copiedConstituentAtomValues role size n P u l r) (s, t, t') = 0
      · rw [hw, mul_zero, hprod]
      · have hrel' : frequencyRoot n t *
            (scheduleAtomRight role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) -
            frequencyRoot n t' *
            (scheduleAtomLeft role ⟨n + 1, copiedConstituentAtomValues role size n P u l r⟩ : ℤ) = s * M := by
          rwa [copiedConstituentAtomValues_right, copiedConstituentAtomValues_left]
        obtain ⟨hn, hg⟩ := fullAtomTransferWeight_forced_node role childBound pivotBound ranges leaf
          n (copiedConstituentAtomValues role size n P u l r) s t t' M hs hrel' hw
        obtain ⟨hL, hR⟩ := hbranches hq
        exact constituentTransferWeight_product role size n P Q childBound pivotBound ranges leaf
          u l r s t t' M hn hg hL hR
    · rw [ite_eq_right hq, mul_zero, hprod]
  · obtain ⟨hl, hr⟩ := mul_ne_zero_iff.mp hprod
    have hr' : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf id u M (r, t') ≠ 0 := by
      intro hz
      exact hr (by rw [hz, map_zero])
    obtain ⟨hn, hg, hq⟩ := constituentTransferWeight_copied_support role size n p hp P hP Q
      childBound pivotBound ranges leaf u l r s t t' M K V hl hr' hs hMpos hMbound hrel
      (hcutL hl).1 (hcutR hr').1 (hcutL hl).2 (hcutR hr').2 hscale hlarge
      (hgap hl hr') (hrange hl hr')
    rw [ite_eq_left hq]
    obtain ⟨hL, hR⟩ := hbranches hq
    exact constituentTransferWeight_product role size n P Q childBound pivotBound ranges leaf
      u l r s t t' M hn hg hL hR

end Ostmann

end OAI

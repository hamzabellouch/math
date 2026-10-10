import OAI.NumberTheory.Ostmann.Construction.ConstituentOriginalAmplitude
import OAI.NumberTheory.Ostmann.Construction.ConstituentBlockProducts
import OAI.NumberTheory.Ostmann.Construction.FullAtomWeightSupport

namespace OAI

/-! # The actual current weight supplies pivot coprimality and frequency units -/

namespace Ostmann

open scoped BigOperators Classical

theorem insertedAtoms_pivot_coprime {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (M : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ)
    (hpair : Pairwise (fun i j => (scheduledInsertedAtoms role n M l u i).Coprime
      (scheduledInsertedAtoms role n M l u j))) :
    M.Coprime ((∏ h, l h) * ∏ y, u y) := by
  have hL : M.Coprime (∏ h, l h) := by
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro h
    have hc := hpair (show scheduledPartitionEquiv role n (.inl ⟨p, hp⟩) ≠
        scheduledPartitionEquiv role n (.inr (.inl h)) from
      by
        intro he
        have hh := (scheduledPartitionEquiv role n).injective he
        cases hh)
    change (scheduledInsertedAtoms role n M l u (scheduledPartitionEquiv role n (.inl ⟨p, hp⟩))).Coprime
      (scheduledInsertedAtoms role n M l u ⟨h.val, h.property.1⟩) at hc
    rwa [scheduledInsertedAtoms_pivot, scheduledInsertedAtoms_H] at hc
  have hU : M.Coprime (∏ y, u y) := by
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro y
    have hc := hpair (show scheduledPartitionEquiv role n (.inl ⟨p, hp⟩) ≠
        scheduledPartitionEquiv role n (.inr (.inr y)) from
      by
        intro he
        have hh := (scheduledPartitionEquiv role n).injective he
        cases hh)
    change (scheduledInsertedAtoms role n M l u (scheduledPartitionEquiv role n (.inl ⟨p, hp⟩))).Coprime
      (scheduledInsertedAtoms role n M l u ⟨y.val, y.property.1⟩) at hc
    rwa [scheduledInsertedAtoms_pivot, scheduledInsertedAtoms_Y] at hc
  exact hL.mul_right hU

theorem constituentCurrentWeight_pivot_coprime {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentCurrentWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    M.Coprime ((∏ h, (a.1 h : ℕ)) * ∏ y, (u y : ℕ)) := by
  have hf := (mul_ne_zero_iff.mp hw).2
  have hs := (fullAtomTransferWeight_top_support role childBound pivotBound ranges leaf n _ (hist a.2) hf).1
  have hc := insertedAtoms_pivot_coprime role n p hp M
    (fun h => ∏ k, (a.1 (constituentH role size n h k) : ℕ))
    (fun y => ∏ k, (u (constituentY role size n y k) : ℕ)) hs
  rwa [constituentH_product role size n (fun h => (a.1 h : ℕ)),
    constituentY_product role size n (fun y => (u y : ℕ))] at hc

theorem constituentCurrentWeight_pivot_frequency_unit {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentCurrentWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    M.Coprime (frequencyRoot n (hist a.2)).natAbs := by
  have hf := (mul_ne_zero_iff.mp hw).2
  have hs := (fullAtomTransferWeight_top_support role childBound pivotBound ranges leaf n _ (hist a.2) hf).2
  have hc := hs (scheduledPartitionEquiv role n (.inl ⟨p, hp⟩))
  rwa [scheduledInsertedAtoms_pivot] at hc

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Construction.ConstituentCharacterCore
import OAI.NumberTheory.Ostmann.Construction.ConstituentUniqueRootEnergy
import OAI.NumberTheory.Ostmann.Construction.ScheduledPhaseNorm

namespace OAI

/-! # Unique-history energy of the actual fixed-pivot character core -/

namespace Ostmann
open scoped BigOperators Classical

theorem retainedGraphRow_norm_le_one {I : Type*} [Fintype I] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (b : Option I → Option I → ℤ)
    (i : I) (M : ZMod p) (x : I → ZMod p) :
    ‖retainedGraphRow χ b i M x‖ ≤ 1 := by
  unfold retainedGraphRow
  rw [norm_mul, norm_prod]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul (character_zpow_norm_le_one _ _ _)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        (fun _ _ => character_zpow_norm_le_one _ _ _))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) zero_le_one
    _ = 1 := one_mul 1

theorem retainedCharacterBranch_norm_le_one {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νH : H → ℂ) (νY : Y → ℂ) (M : ℕ)
    (hH : ∀ h, ‖νH h‖ ≤ 1) (hY : ∀ y, ‖νY y‖ ≤ 1) :
    ‖retainedCharacterBranch L U χH χY b νH νY M‖ ≤ 1 := by
  unfold retainedCharacterBranch
  rw [norm_mul, norm_prod, norm_prod]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul ?_ ?_
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) zero_le_one
    _ = 1 := one_mul 1
  · apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro h _
    rw [norm_mul]
    exact (mul_le_mul (hH h) (retainedGraphRow_norm_le_one _ _ _ _ _)
      (norm_nonneg _) zero_le_one).trans (one_mul 1).le
  · apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro y _
    rw [norm_mul]
    exact (mul_le_mul (hY y) (retainedGraphRow_norm_le_one _ _ _ _ _)
      (norm_nonneg _) zero_le_one).trans (one_mul 1).le

section
variable {I D R : Type*} [Fintype I] [Fintype D] [Fintype R]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
variable (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)

omit [Fintype D] in
include hP in
theorem constituentCharacterCore_norm_le_full (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D) :
    ‖constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M (l, d)‖ ≤
      ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ := by
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  unfold constituentCharacterCore
  rw [norm_mul]
  have hb := retainedCharacterBranch_norm_le_one (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
    (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
    (scheduledRetainedGraph (fun i : Σ a, Fin (size a) => role i.1) initialCompleteGraph pivot n)
    _ _ M
    (fun h => copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _
      (initialRegularUnary_norm_le_one χ κ hκ) n (hist d) h.val (l h))
    (fun y => copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _
      (initialRegularUnary_norm_le_one χ κ hκ) n (hist d) y.val (u y))
  apply (mul_le_of_le_one_right (norm_nonneg _) hb).trans
  unfold constituentUnweightedTransferWeight
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg _

omit [Fintype D] in
include hP in
theorem constituentCharacterCore_nonzero_valid
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D)
    (h : constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M (l, d) ≠ 0) :
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, scheduledInsertedAtoms role n M
        (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))⟩ (hist d) := by
  unfold constituentCharacterCore at h
  have hw := (mul_ne_zero_iff.mp h).1
  unfold constituentUnweightedTransferWeight at hw
  split_ifs at hw
  · exact (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n _ _ hw).2
  · exact False.elim (hw rfl)

include hP in
theorem constituentCharacterCore_root_energy (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d e, root d = root e → frequencyRoot n (hist d) = frequencyRoot n (hist e))
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) :
    (∑ s, ‖rootFibreSum root s (fun d =>
      constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M (l, d))‖ ^ 2) ≤
      ∑ d, ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ ^ 2 := by
  rw [rootFibreSum_energy_of_unique root _ (fun d e hd he hr => ?_)]
  · exact Finset.sum_le_sum fun d _ => pow_le_pow_left₀ (norm_nonneg _)
      (constituentCharacterCore_norm_le_full role size χ κ pivot n P hP
        childBound pivotBound ranges leaf hist u M hκ l d) 2
  · apply hhist
    exact validTransferHistory_unique (scheduleAtomSystem role childBound pivotBound) n _ _ _
      (constituentCharacterCore_nonzero_valid role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M l d hd)
      (constituentCharacterCore_nonzero_valid role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M l e he)
      (hroot d e hr)

end
end Ostmann

end OAI

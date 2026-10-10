import OAI.NumberTheory.Ostmann.Construction.ConstituentRootCoefficient
import OAI.NumberTheory.Ostmann.Construction.TransferHistorySquare

namespace OAI

/-! # Unique histories remove multiplicity from the actual final energy -/

namespace Ostmann
open scoped BigOperators Classical

private theorem norm_sum_sq_of_unique {D : Type*} [Fintype D] (F : D → ℂ)
    (hu : ∀ d e, F d ≠ 0 → F e ≠ 0 → d = e) :
    ‖∑ d, F d‖ ^ 2 = ∑ d, ‖F d‖ ^ 2 := by
  by_cases hf : ∃ d, F d ≠ 0
  · obtain ⟨d, hd⟩ := hf
    have he (e) (hne : e ≠ d) : F e = 0 := by
      by_contra h
      exact hne (hu e d h hd)
    rw [Fintype.sum_eq_single d he, Fintype.sum_eq_single d]
    intro e hne
    simp only [he e hne, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · push Not at hf
    simp only [hf, Finset.sum_const_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem rootFibreSum_energy_of_unique {D R : Type*} [Fintype D] [Fintype R]
    (root : D → R) (F : D → ℂ)
    (hu : ∀ d e, F d ≠ 0 → F e ≠ 0 → root d = root e → d = e) :
    (∑ s, ‖rootFibreSum root s F‖ ^ 2) = ∑ d, ‖F d‖ ^ 2 := by
  have hi (s : R) : ‖rootFibreSum root s F‖ ^ 2 =
      ∑ d, if root d = s then ‖F d‖ ^ 2 else 0 := by
    unfold rootFibreSum
    rw [norm_sum_sq_of_unique]
    · apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    · intro d e hd he
      have hds : root d = s := by by_contra h; simp only [h, ite_false, ne_eq, not_true_eq_false] at hd
      have hes : root e = s := by by_contra h; simp only [h, ite_false, ne_eq, not_true_eq_false] at he
      exact hu d e (by simpa only [hds, ite_true] using hd)
        (by simpa only [hes, ite_true] using he) (hds.trans hes.symm)
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp

section
variable {I D R : Type*} [Fintype I] [Fintype D] [Fintype R]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (center : ∀ p : ℕ, ZMod p)

include hP in
theorem constituentPrimeTerm_nonzero_valid (t : FrequencyTree ℤ n)
    (q : SurvivingConstituent role size n → P)
    (h : constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
      leaf center t q ≠ 0) :
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod⟩ t := by
  have hw := (mul_ne_zero_iff.mp h).1
  exact (fullAtomTransferWeight_support role childBound pivotBound ranges leaf n _ t hw).2

theorem constituentPrimeRootCoefficient_unique_energy
    (hist : D → FrequencyTree ℤ n) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d e, root d = root e → frequencyRoot n (hist d) = frequencyRoot n (hist e))
    (q : SurvivingConstituent role size n → P) :
    (∑ s, ‖constituentPrimeRootCoefficient role size χ κ pivot n P hP childBound pivotBound
      ranges leaf center hist root s q‖ ^ 2) =
      ∑ d, ‖constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound
        ranges leaf center (hist d) q‖ ^ 2 := by
  apply rootFibreSum_energy_of_unique
  intro d e hd he hr
  apply hhist
  exact validTransferHistory_unique (scheduleAtomSystem role childBound pivotBound) n _ _ _
    (constituentPrimeTerm_nonzero_valid role size χ κ pivot n P hP childBound pivotBound
      ranges leaf center (hist d) q hd)
    (constituentPrimeTerm_nonzero_valid role size χ κ pivot n P hP childBound pivotBound
      ranges leaf center (hist e) q he) (hroot d e hr)

include hP in
theorem constituentPrimeTerm_square_le_weight (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (t : FrequencyTree ℤ n) (q : SurvivingConstituent role size n → P) :
    ‖constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
      leaf center t q‖ ^ 2 ≤
    ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod) t‖ ^ 2 := by
  unfold constituentPrimeTerm
  by_cases hp : Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ))
  · rw [ite_eq_left hp, norm_mul, mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _)
      (scheduledSamplePhase_norm_le_one (fun i : Σ a, Fin (size a) => role i.1)
        χ κ hκ pivot n t P hP q center))
  · simp only [hp, ite_false, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

theorem constituentPrimeRootCoefficient_mean_energy_unique
    (Q : (Σ i, Fin (size i)) → Finset ℕ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (hist : D → FrequencyTree ℤ n) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d e, root d = root e → frequencyRoot n (hist d) = frequencyRoot n (hist e)) :
    (∑ s, ∑ q : SurvivingConstituent role size n → P,
      (∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) *
        ‖constituentPrimeRootCoefficient role size χ κ pivot n P hP childBound pivotBound
          ranges leaf center hist root s q‖ ^ 2) ≤
    ∑ d, ∑ q : SurvivingConstituent role size n → P,
      (∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) *
        ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod) (hist d)‖ ^ 2 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, constituentPrimeRootCoefficient_unique_energy role size χ κ
    pivot n P hP childBound pivotBound ranges leaf center hist hhist root hroot, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d _
  apply Finset.sum_le_sum
  intro q _
  exact mul_le_mul_of_nonneg_left
    (constituentPrimeTerm_square_le_weight role size χ κ pivot n P hP childBound pivotBound
      ranges leaf center hκ (hist d) q)
    (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg _ _ _))

end
end Ostmann

end OAI

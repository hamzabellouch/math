import OAI.NumberTheory.Ostmann.Construction.ConstituentSupportedMatchingEnergy

namespace OAI

/-! # Averaging matching families with the original single outside prime law -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem constituent_matching_family_energy_on_product {I D R : Type*}
    [Fintype I] [Fintype D] [Fintype R]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' → frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (M : ℕ)
    (S : Finset (Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)))
    (lower : ℝ) (hlower : 0 < lower)
    (hproduct : ∀ (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P)
      (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D),
      fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d) ≠ 0 →
      lower ≤ ∏ h, (l h : ℝ)) :
    ‖∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
      ((∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y) : ℝ) : ℂ) *
      ∑ e ∈ S, ∑ d : D, ∑ d' : D, if root d = root d' then
      ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
        constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M (l, d) *
        conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
          childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) else 0‖ ≤
      (S.card : ℝ) * ((∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹) *
      ∑ u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P,
        (∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)) *
        ∑ d : D, ∑ l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P,
        (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
        ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (scheduledInsertedAtoms role n M
            (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
            (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ ^ 2 := by
  let H := CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n
  let Y := CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n
  let μ := fun u : Y → P => ∏ y, primeSubsetPrior P (Q (copyScheduleOrigin n y.val)) (u y)
  let A₀ := (∏ h : H, (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) * lower⁻¹
  let F := fun (e : Equiv.Perm H) (u : Y → P) =>
    ∑ d : D, ∑ d' : D, if root d = root d' then ∑ l : H → P,
      constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCoefficient role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist u M (l ∘ e.symm, d')) else 0
  let E := fun u : Y → P => ∑ d : D, ∑ l : H → P,
    (∏ h, primeSubsetPrior P (Q (copyScheduleOrigin n h.val)) (l h)) *
    ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ ^ 2
  have hμ (u) : 0 ≤ μ u := Finset.prod_nonneg (fun _ _ => primeSubsetPrior_nonneg _ _ _)
  have hf (e : Equiv.Perm H) (u : Y → P) : ‖F e u‖ ≤ A₀ * E u :=
    constituent_matching_energy_on_product role size χ κ pivot hκ n P hP Q childBound pivotBound
      ranges leaf hist hhist root hroot u M e lower hlower (hproduct u)
  change ‖∑ u : Y → P, (μ u : ℂ) * ∑ e ∈ S, F e u‖ ≤
    (S.card : ℝ) * A₀ * ∑ u, μ u * E u
  calc
    _ ≤ ∑ u : Y → P, ‖(μ u : ℂ) * ∑ e ∈ S, F e u‖ := norm_sum_le _ _
    _ ≤ ∑ u : Y → P, μ u * ∑ e ∈ S, ‖F e u‖ := by
      apply Finset.sum_le_sum
      intro u _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ u)]
      exact mul_le_mul_of_nonneg_left (norm_sum_le S _) (hμ u)
    _ ≤ ∑ u : Y → P, μ u * ∑ _e ∈ S, A₀ * E u := by
      apply Finset.sum_le_sum
      intro u _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e _ => hf e u)) (hμ u)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      simp_rw [show ∀ u : Y → P, μ u * ((S.card : ℝ) * (A₀ * E u)) =
        ((S.card : ℝ) * A₀) * (μ u * E u) by intro u; ring]
      exact (Finset.mul_sum _ _ _).symm

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Characters.PivotProductPrior
import OAI.NumberTheory.Ostmann.Preliminaries.SubprobabilityTransfer

namespace OAI

/-! # Extending an internally distinct pivot total to all integers -/

namespace Ostmann

open scoped BigOperators Classical

/-- The row can depend on the entire pivot tuple. Its coefficient depends
only on the total, so no character on the extended integer is introduced. -/
theorem pivot_integer_transfer (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (row : ∀ x : Fin n → P, Fin (∏ i, (x i : ℕ)) → ℂ)
    (hrow : ∀ x ∈ S, ∀ u, ‖row x u‖ ≤ 1)
    (B : ∀ M : ℕ, Fin M → ℂ) :
    ‖∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
        ∑ u, row x u * B (∏ i, (x i : ℕ)) u‖ ^ 2 ≤
      ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) *
        ∑ M ∈ T, ∑ u, ‖B M u‖ ^ 2 := by
  let μ := fun x : Fin n → P => productPrior (fun i => primeSubsetPrior P (Q i)) x
  let F := fun M : ℕ => ∑ u, ‖B M u‖ ^ 2
  let K := (n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹
  have hμ : ∀ x, 0 ≤ μ x := fun x => productPrior_nonneg _ (fun i p => primeSubsetPrior_nonneg _ _ p) x
  have hF : ∀ M, 0 ≤ F M := fun M => Finset.sum_nonneg (fun u _ => sq_nonneg _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmass : (∑ x : S, μ x) ≤ 1 := by
    rw [Finset.sum_coe_sort S μ]
    calc
      _ ≤ ∑ x, μ x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun x _ _ => hμ x)
      _ = 1 := productPrior_mass _ (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQ i))
  have hr : ∀ x : S, (∑ u, ‖row x u‖ ^ 2) ≤ (∏ i, (x.val i : ℕ)) := by
    intro x
    calc
      _ ≤ ∑ _u : Fin (∏ i, (x.val i : ℕ)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro u _
        have hh := hrow x x.property u
        nlinarith [norm_nonneg (row x u)]
      _ = _ := by simp
  have hcs := subprobability_transfer_row_bound (fun x : S => μ x) (fun x => hμ x) hmass
    (fun x : S => row x) (fun x : S => B (∏ i, (x.val i : ℕ)))
    (fun x : S => ((∏ i, (x.val i : ℕ)) : ℝ))
    (by simpa only [Nat.cast_prod] using hr)
  have hext : (∑ x ∈ S, μ x * ((∏ i, (x i : ℕ)) * F (∏ i, (x i : ℕ)))) ≤
      K * ∑ M ∈ T, F M := by
    rw [← Finset.sum_fiberwise_of_maps_to hT, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro M hMT
    calc
      _ = (∑ x ∈ S.filter (fun x => (∏ i, (x i : ℕ)) = M), μ x) * ((M : ℝ) * F M) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ ≤ (K * (M : ℝ)⁻¹) * ((M : ℝ) * F M) := by
        exact mul_le_mul_of_nonneg_right (harmonic_distinct_product_mass P hP Q S hS M)
          (mul_nonneg (Nat.cast_nonneg M) (hF M))
      _ ≤ K * F M := by
        by_cases hM : M = 0
        · simp only [hM, Nat.cast_zero, inv_zero, mul_zero, zero_mul]
          exact mul_nonneg hK (hF 0)
        · have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM
          exact le_of_eq (by field_simp)
  have hcs' : ‖∑ x ∈ S, (μ x : ℂ) * ∑ u, row x u * B (∏ i, (x i : ℕ)) u‖ ^ 2 ≤
      ∑ x ∈ S, μ x * ((∏ i, (x i : ℕ)) * F (∏ i, (x i : ℕ))) := by
    have hs₁ := Finset.sum_coe_sort S (fun x : Fin n → P =>
      (μ x : ℂ) * ∑ u, row x u * B (∏ i, (x i : ℕ)) u)
    have hs₂ := Finset.sum_coe_sort S (fun x : Fin n → P =>
      μ x * ((∏ i, (x i : ℕ)) * F (∏ i, (x i : ℕ))))
    rw [← hs₁, ← hs₂]
    simpa only [Nat.cast_prod, F] using hcs
  exact hcs'.trans hext

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Characters.WeightedPhaseExtraction

namespace OAI

/-! # Products of the original smooth factors retain finite variation -/

namespace Ostmann

open scoped BigOperators

theorem discreteVariation_mul (f g : ℕ → ℂ) (B D : ℝ) (N : ℕ)
    (hD : 0 ≤ D) (hf : ∀ j, ‖f j‖ ≤ B) (hg : ∀ j, ‖g j‖ ≤ D) :
    discreteVariation (fun j => f j * g j) N ≤
      B * discreteVariation g N + D * discreteVariation f N := by
  have hend : ‖f (N - 1) * g (N - 1)‖ ≤ B * ‖g (N - 1)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
  have hstep (j : ℕ) : ‖f (j + 1) * g (j + 1) - f j * g j‖ ≤
      B * ‖g (j + 1) - g j‖ + D * ‖f (j + 1) - f j‖ := by
    rw [show f (j + 1) * g (j + 1) - f j * g j =
      f (j + 1) * (g (j + 1) - g j) + (f (j + 1) - f j) * g j by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)
    · simpa only [mul_comm D] using mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
  have hs := Finset.sum_le_sum (s := Finset.range (N - 1)) (fun j _ => hstep j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  unfold discreteVariation
  nlinarith [mul_nonneg hD (norm_nonneg (f (N - 1)))]

theorem discreteVariation_prod (n : ℕ) (f : Fin n → ℕ → ℂ) (B V : Fin n → ℝ) (N : ℕ)
    (hB : ∀ i, 0 ≤ B i) (hV : ∀ i, 0 ≤ V i)
    (hf : ∀ i j, ‖f i j‖ ≤ B i) (hv : ∀ i, discreteVariation (f i) N ≤ V i) :
    discreteVariation (fun j => ∏ i, f i j) N ≤ ∏ i, (B i + V i) := by
  induction n with
  | zero => simp [discreteVariation]
  | succ n ih =>
    let g : ℕ → ℂ := fun j => ∏ i : Fin n, f i.succ j
    let C : ℝ := ∏ i : Fin n, B i.succ
    let E : ℝ := ∏ i : Fin n, (B i.succ + V i.succ)
    have hC : 0 ≤ C := Finset.prod_nonneg fun i _ => hB i.succ
    have hg (j : ℕ) : ‖g j‖ ≤ C := by
      change ‖∏ i : Fin n, f i.succ j‖ ≤ C
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hf i.succ j)
    have hCE : C ≤ E := Finset.prod_le_prod₀ (fun i _ => hB i.succ)
      (fun i _ => le_add_of_nonneg_right (hV i.succ))
    have hvg : discreteVariation g N ≤ E := ih (fun i => f i.succ) (fun i => B i.succ)
      (fun i => V i.succ) (fun i => hB i.succ) (fun i => hV i.succ)
      (fun i => hf i.succ) (fun i => hv i.succ)
    have hp : (fun j => ∏ i, f i j) = fun j => f 0 j * g j := by
      funext j
      exact Fin.prod_univ_succ _
    rw [hp, Fin.prod_univ_succ]
    apply (discreteVariation_mul (f 0) g (B 0) C N hC (hf 0) hg).trans
    calc
      _ ≤ B 0 * E + C * V 0 := add_le_add
        (mul_le_mul_of_nonneg_left hvg (hB 0)) (mul_le_mul_of_nonneg_left (hv 0) hC)
      _ ≤ B 0 * E + E * V 0 := add_le_add le_rfl (mul_le_mul_of_nonneg_right hCE (hV 0))
      _ = _ := by change B 0 * E + E * V 0 = (B 0 + V 0) * E; ring

end Ostmann

end OAI

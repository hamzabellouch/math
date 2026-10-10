import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightFourier

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]

theorem norm_deriv_finsetProd_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → 𝕜) (f' : ι → 𝕜) (B : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ S, HasDerivAt (f i) (f' i) x)
    (hn : ∀ i ∈ S, ‖f i x‖ ≤ 1) (hd : ∀ i ∈ S, ‖f' i‖ ≤ B i) :
    ‖deriv (fun t => ∏ i ∈ S, f i t) x‖ ≤ ∑ i ∈ S, B i := by
  rw [(HasDerivAt.fun_finsetProd hf).deriv]
  calc
    _ ≤ ∑ i ∈ S, ‖(∏ j ∈ S.erase i, f j x) • f' i‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [smul_eq_mul,norm_mul]
      have hp : ‖∏ j ∈ S.erase i, f j x‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j hj => hn j (Finset.mem_of_mem_erase hj))
      calc
        _ ≤ 1 * B i := mul_le_mul hp (hd i hi) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _

theorem norm_deriv_finsetProd_le_common {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → 𝕜) (f' : ι → 𝕜) (A D x : ℝ)
    (hA : 1 ≤ A) (_hD : 0 ≤ D)
    (hf : ∀ i ∈ S, HasDerivAt (f i) (f' i) x)
    (hn : ∀ i ∈ S, ‖f i x‖ ≤ A) (hd : ∀ i ∈ S, ‖f' i‖ ≤ D) :
    ‖deriv (fun t => ∏ i ∈ S, f i t) x‖ ≤ (S.card:ℝ) * A^S.card * D := by
  rw [(HasDerivAt.fun_finsetProd hf).deriv]
  calc
    _ ≤ ∑ i ∈ S, ‖(∏ j ∈ S.erase i, f j x) • f' i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, A^S.card * D := by
      apply Finset.sum_le_sum
      intro i hi
      rw [smul_eq_mul,norm_mul]
      have hp : ‖∏ j ∈ S.erase i, f j x‖ ≤ A^S.card := by
        rw [norm_prod]
        calc
          _ ≤ ∏ j ∈ S.erase i, A := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            (fun j hj => hn j (Finset.mem_of_mem_erase hj))
          _ = A^(S.erase i).card := by simp only [Finset.prod_const]
          _ ≤ _ := pow_le_pow_right₀ hA (Finset.card_erase_le)
      exact mul_le_mul hp (hd i hi) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hA) _)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; ring

end Ostmann.Arithmetic

end

end OAI

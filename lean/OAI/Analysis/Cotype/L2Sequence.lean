import OAI.Analysis.Cotype.L2MomentLifts
import Mathlib.Analysis.Normed.Lp.lpSpace

namespace OAI

noncomputable section

open scoped BigOperators ENNReal
namespace Cotype
variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

omit [(i : ι) → NormedSpace ℝ (E i)] in
theorem lp_two_summable_sq (z : lp E 2) : Summable (fun i => ‖z i‖^2) := by
  simpa using (lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

omit [(i : ι) → NormedSpace ℝ (E i)] in
theorem lp_two_norm_sq (z : lp E 2) : ‖z‖^2 = ∑' i, ‖z i‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) z

omit [(i : ι) → NormedSpace ℝ (E i)] in
theorem mem_lp_two_of_summable_sq (z : ∀ i, E i) (hz : Summable (fun i => ‖z i‖^2)) :
    Memℓp z 2 := by
  apply memℓp_gen
  simpa using hz

omit [(i : ι) → NormedSpace ℝ (E i)] in
theorem cubeL2_lp_sq {m : ℕ} (H : Cube m → lp E 2) :
    cubeL2 (lp E 2) H ^ 2 = ∑' i, cubeL2 (E i) (fun ε => H ε i)^2 := by
  simp only [cubeL2_sq, lp_two_norm_sq, average, smul_eq_mul]
  rw [tsum_mul_left]
  congr 1
  exact (Summable.tsum_finsetSum (fun ε _ => lp_two_summable_sq (H ε))).symm

theorem norm_sq_le_card_cubeL2_sq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m : ℕ} (H : Cube m → X) (ε : Cube m) :
    ‖H ε‖^2 ≤ (Fintype.card (Cube m) : ℝ) * cubeL2 X H^2 := by
  rw [cubeL2_sq]
  have hc : (Fintype.card (Cube m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [average, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  exact Finset.single_le_sum (fun a _ => sq_nonneg ‖H a‖) (Finset.mem_univ ε)

end Cotype

end

end OAI

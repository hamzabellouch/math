import Mathlib
import OAI.Analysis.Conductivity.Walls.SeamL2

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma seamLayer_scaled_tendsto_of_cubic {τ u : R3 → ℝ} (_ : MemLp u 2 volume)
    {δ A : ℝ} (hδ : 0<δ)
    (hbound : ∀ ε,0<ε → ε≤δ → (∫ x in {x | 0<τ x ∧ τ x≤ε},u x^2)≤A*ε^3) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*∫ x in seamLayer τ n,u x^2) atTop (𝓝 0) := by
  have hn (n : ℕ) : 0<(n:ℝ)+1 := by positivity
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  have he : ∀ᶠ n : ℕ in atTop,2/((n:ℝ)+1)≤δ := by
    have hh := ht.const_mul 2
    simp only [mul_zero] at hh
    simpa only [←div_eq_mul_inv] using (hh.eventually (gt_mem_nhds hδ)).mono (fun _ h => h.le)
  have hlim := ht.const_mul (8*A)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => sq_nonneg _)))) _ hlim
  filter_upwards [he] with n hnδ
  have hs : seamLayer τ n={x | 0<τ x ∧ τ x≤2/((n:ℝ)+1)} := by
    ext x
    exact and_congr_right (fun _ => by rw [le_div_iff₀ (hn n),mul_comm])
  rw [hs]
  have hb := mul_le_mul_of_nonneg_left (hbound _ (div_pos (by norm_num) (hn n)) hnδ) (sq_nonneg ((n:ℝ)+1))
  apply hb.trans_eq
  field_simp
  ring

end ScalarConductivity

end
end

end OAI

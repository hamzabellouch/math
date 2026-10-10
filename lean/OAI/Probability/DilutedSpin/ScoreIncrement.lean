import OAI.Probability.DilutedSpin.ReservoirTrees

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology

lemma scoreScale_succ_sub_sharp {N : ℕ} (hN : 0 < N) :
    scoreScale (N+1)-scoreScale N ≤ scoreScale N/N := by
  have hx : (0:ℝ)<N := by exact_mod_cast hN
  have hy : (0:ℝ) ≤ 1+1/(N:ℝ) := by positivity
  have hxy : (N:ℝ)+1=(N:ℝ)*(1+1/(N:ℝ)) := by field_simp
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_self_of_one_le (show (1:ℝ)≤1+1/(N:ℝ) from le_add_of_nonneg_right (by positivity))
      (show (3:ℝ)/4≤1 by norm_num)) (Real.rpow_nonneg hx.le ((3:ℝ)/4))
  unfold scoreScale
  rw [Nat.cast_add,Nat.cast_one,hxy,Real.mul_rpow hx.le hy]
  calc
    _ ≤ (N:ℝ)^((3:ℝ)/4)*(1+1/(N:ℝ))-(N:ℝ)^((3:ℝ)/4) := sub_le_sub_right h _
    _ = _ := by ring

lemma scoreScale_succ_difference_tendsto :
    Tendsto (fun N => scoreScale (N+1)-scoreScale N) atTop (𝓝 0) := by
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp he
  apply squeeze_zero' (eventually_atTop.2 ⟨1,fun N _ => sub_nonneg.mpr (scoreScale_mono (Nat.le_succ N))⟩)
    (eventually_atTop.2 ⟨1,fun N hN => ?_⟩) ht
  change scoreScale (N+1)-scoreScale N ≤ (N:ℝ)^(-(1/4:ℝ))
  rw [← neg_div]
  rw [← SizeCoupling.scoreScale_div (show 0 < N by omega)]
  exact scoreScale_succ_sub_sharp (by omega)

end DilutedSpinGlass

end

end OAI

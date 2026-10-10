import OAI.InformationTheory.BooleanNoise.Comparison
import OAI.InformationTheory.SoftChannel.Production

namespace OAI

section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem Comparison_sq_lt_one_of_mem {u : ℝ} (hu : u ∈ Ioo (-1) 1) : u ^ 2 < 1 := by
  have hp : 0 < (1 - u) * (u + 1) := mul_pos (by linarith [hu.2]) (by linarith [hu.1])
  nlinarith

theorem Comparison_hasDerivAt_artanh_cubic_gap {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt (fun x : ℝ => Real.artanh x - x - x ^ 3 / 3)
      (u ^ 4 / (1 - u ^ 2)) u := by
  have hden : 1 - u ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr (Comparison_sq_lt_one_of_mem hu))
  convert! ((hasDerivAt_artanh hu).sub (hasDerivAt_id u)).sub
    (((hasDerivAt_id u).pow 3).div_const 3) using 1
  simp only [id_eq]
  field_simp [hden]
  ring

theorem Comparison_exp_neg_log_five : Real.exp (-Real.log 5) = (1 / 5 : ℝ) := by
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

end LeanBlast.CourtadeKumar
end
end

end OAI

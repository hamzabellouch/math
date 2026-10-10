import OAI.Combinatorics.Progressions.Sampling.SquareSamplingAccuracy

namespace OAI

section

namespace Erdos3

noncomputable def affineSquareErrorAccuracy (target capLog : ℝ) : ℝ :=
  Real.exp (-(target + capLog + 24))

theorem affineSquareErrorAccuracy_pos (target capLog : ℝ) :
    0 < affineSquareErrorAccuracy target capLog := Real.exp_pos _

theorem affineSquareErrorAccuracy_inv (target capLog : ℝ) :
    (affineSquareErrorAccuracy target capLog)⁻¹ = Real.exp (target + capLog + 24) := by
  rw [affineSquareErrorAccuracy, ← Real.exp_neg, neg_neg]

theorem affineSquareErrorAccuracy_bound {target capLog cap e₁ e₂ e₃ : ℝ}
    (hcap0 : 0 ≤ cap) (hcap : cap ≤ Real.exp capLog)
    (h₁ : e₁ ≤ affineSquareErrorAccuracy target capLog)
    (h₂ : e₂ ≤ affineSquareErrorAccuracy target capLog)
    (h₃ : e₃ ≤ affineSquareErrorAccuracy target capLog) :
    cap * (e₁ + e₂ + e₃) ≤ Real.exp (-(target + 20)) := by
  have hb := (affineSquareErrorAccuracy_pos target capLog).le
  have he : e₁ + e₂ + e₃ ≤ 3 * affineSquareErrorAccuracy target capLog := by
    linarith only [h₁, h₂, h₃]
  have h3 : (3 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ cap * (3 * affineSquareErrorAccuracy target capLog) := mul_le_mul_of_nonneg_left he hcap0
    _ ≤ Real.exp capLog * (Real.exp 4 * affineSquareErrorAccuracy target capLog) := by gcongr
    _ = _ := by
      unfold affineSquareErrorAccuracy
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

end OAI

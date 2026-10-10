import OAI.MeasureTheory.Falconer.Slicing.GaussianLossAbsorption

namespace OAI

/-! # One scale choice supplies every scalar inequality in the planar slice application -/

namespace Falconer
open Real Filter
open scoped Topology

theorem inverse_power_gap {δ η H : ℝ} (hδ : 0 < δ) (hH : 0 < H)
    (hgap : H < δ^(-η)) : δ^η < 1/H := by
  apply (lt_div_iff₀ hH).mpr
  calc
    δ^η*H < δ^η*δ^(-η) := mul_lt_mul_of_pos_left hgap (Real.rpow_pos_of_pos hδ η)
    _ = 1 := by
      rw [Real.rpow_neg hδ.le]
      exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hδ η))

theorem eventually_gaussian_planar_loss_budget {η : ℝ} (hη : 0 < η)
    {V a : ℝ} (hV : 1 ≤ V) (ha : 1 ≤ a) (f b A K₀ : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ K₀ ≤ δ^(-(η/100)) ∧
      1 ≤ 4*(δ^(-(η/100)))^10*V ∧
      (4*(δ^(-(η/100)))^10*V)*(4*a)^f ≤ δ^(-η) ∧
      (4*(δ^(-(η/100)))^10*V)*(8*a)^b ≤ δ^(-η) ∧
      δ^η < 1/(4*(δ^(-(η/100)))^10*V) ∧
      A*(δ^(-(η/100)))^12*δ^(-b) ≤ δ^(-b-η) := by
  let W : ℝ := V*((4*a)^f+(8*a)^b+1)
  have hVpos : 0 < V := by linarith
  have ha0 : 0 < a := by linarith
  have hfpos : 0 < (4*a)^f := Real.rpow_pos_of_pos (by positivity) _
  have hbpos : 0 < (8*a)^b := Real.rpow_pos_of_pos (by positivity) _
  have hVW : V < W := by dsimp [W]; nlinarith
  have hpf : V*(4*a)^f ≤ W := by dsimp [W]; nlinarith
  have hqb : V*(8*a)^b ≤ W := by dsimp [W]; nlinarith
  filter_upwards [eventually_gaussian_scale_losses hη (max K₀ 1) W A b]
    with δ hδ
  rcases hδ with ⟨hδ,hK,hgap,hcover⟩
  have hK₀ : K₀ ≤ δ^(-(η/100)) := (le_max_left _ _).trans hK
  have hK1 : 1 ≤ δ^(-(η/100)) := (le_max_right _ _).trans hK
  have hKpow : 1 ≤ (δ^(-(η/100)))^10 := one_le_pow₀ hK1
  have hH : 0 < 4*(δ^(-(η/100)))^10*V := by positivity
  have hHW : 4*(δ^(-(η/100)))^10*V < δ^(-η) := by
    apply lt_trans _ hgap
    nlinarith [Real.rpow_pos_of_pos hδ (-(η/100))]
  refine ⟨hδ,hK₀,?_,?_,?_,inverse_power_gap hδ hH hHW,hcover⟩
  · nlinarith
  · apply le_trans _ hgap.le
    nlinarith [pow_nonneg (Real.rpow_nonneg hδ.le (-(η/100))) 10]
  · apply le_trans _ hgap.le
    nlinarith [pow_nonneg (Real.rpow_nonneg hδ.le (-(η/100))) 10]

end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Geometry.ScalarGridGainAlgebra

namespace OAI

/-! The power margins in the product-potential argument. -/
namespace Falconer

 theorem grid_gain_count_rate {δ N κ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hN : 0 < N) (hmargin : 3*ε ≤ κ) (hself : 1 ≤ δ^(κ-ε)*N) :
    1/N ≤ δ^(2*ε) := by
  have hc : 1/N ≤ δ^(κ-ε) := (div_le_iff₀ hN).2 hself
  exact hc.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))

 theorem grid_gain_volume_rate {δ N σ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hmargin : 4*ε ≤ 1-σ) (hε : 0 ≤ ε) (hupper : N ≤ δ^(-σ-ε)) :
    δ*N ≤ δ^(2*ε) ∧ δ*N ≤ δ^((1-σ)/2) := by
  have hv : δ*N ≤ δ^(1-σ-ε) := by
    calc
      _ ≤ δ*δ^(-σ-ε) := mul_le_mul_of_nonneg_left hupper hδ.le
      _ = δ^(1 : ℝ)*δ^(-σ-ε) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
  exact ⟨hv.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)),
    hv.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))⟩

 theorem grid_gain_weight_rate {δ N σ θ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hN : 0 < N) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2) (hε : 0 ≤ ε)
    (hmargin : 8*ε ≤ (1-2*θ)*(1-σ))
    (hvolume : δ*N ≤ δ^((1-σ)/2)) :
    (δ^(-ε))^(2*(1-θ))*(δ*N)^(1-2*θ) ≤ δ^(2*ε) := by
  have hq : 0 ≤ 1-2*θ := by linarith
  have hw := Real.rpow_le_rpow (mul_pos hδ hN).le hvolume hq
  calc
    _ ≤ (δ^(-ε))^(2*(1-θ))*(δ^((1-σ)/2))^(1-2*θ) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = δ^((-ε)*(2*(1-θ))+(1-σ)/2*(1-2*θ)) := by
      rw [← Real.rpow_mul hδ.le,← Real.rpow_mul hδ.le,← Real.rpow_add hδ]
    _ ≤ δ^(2*ε) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)

 theorem scalar_ball_self_bound {δ K κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      ((X.filter fun x => |x-u| ≤ r).card : ℝ) ≤ K*r^κ*(X.card : ℝ)) :
    1 ≤ K*δ^κ*(X.card : ℝ) := by
  classical
  obtain ⟨x,hx⟩ := hX
  have hm : x ∈ X.filter (fun y => |y-x| ≤ δ) := by
    simp only [Finset.mem_filter]
    exact ⟨hx,by simpa using hδ.le⟩
  have hc : (1 : ℝ) ≤ ((X.filter fun y => |y-x| ≤ δ).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨x,hm⟩
  exact hc.trans (hball x δ le_rfl hδ1)

end Falconer

end OAI

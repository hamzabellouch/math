import OAI.MeasureTheory.Falconer.Measures.ScalarProductBalls

namespace OAI

/-! Interpolating the fine packing bound with scalar nonconcentration
gives a higher-dimensional ball exponent for the actual product set. -/
namespace Falconer

theorem nonnegative_bound_interpolation {x a b θ : ℝ} (hx : 0 ≤ x)
    (ha : x ≤ a) (hb : x ≤ b) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ≤ a^θ*b^(1-θ) := by
  by_cases hx0 : x = 0
  · rw [hx0]
    exact mul_nonneg (Real.rpow_nonneg (hx.trans ha) _) (Real.rpow_nonneg (hx.trans hb) _)
  have hxpos : 0 < x := lt_of_le_of_ne hx (by intro h; exact hx0 h.symm)
  calc
    x = x^θ*x^(1-θ) := by
      rw [← Real.rpow_add hxpos,show θ+(1-θ) = (1 : ℝ) by ring,Real.rpow_one]
    _ ≤ _ := mul_le_mul (Real.rpow_le_rpow hx ha hθ)
      (Real.rpow_le_rpow hx hb (sub_nonneg.mpr hθ1))
      (Real.rpow_nonneg hx _) (Real.rpow_nonneg (hx.trans ha) _)

theorem scalarProductPoints_interpolated_ball {δ r K κ θ : ℝ}
    (hδ : 0 < δ) (hr : δ ≤ r) (hK : 0 ≤ K) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (X : Finset ℝ) (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (z : Space 2)
    (hball : ∀ u : ℝ, ((X.filter fun x => |x-u| ≤ r).card : ℝ) ≤ K*r^κ*(X.card : ℝ)) :
    (((scalarProductPoints X X).filter fun p => dist p z ≤ r).card : ℝ) ≤
      (81*(r/δ)^2)^θ*((K*r^κ*(X.card : ℝ))^2)^(1-θ) := by
  have hcount : (((scalarProductPoints X X).filter fun p => dist p z ≤ r).card : ℝ) ≤
      ((X.filter fun x => |x-z 0| ≤ r).card : ℝ)*((X.filter fun y => |y-z 1| ≤ r).card : ℝ) := by
    exact_mod_cast scalarProductPoints_ball_card X X z r
  have hr0 : 0 ≤ r := hδ.le.trans hr
  have hweak : (((scalarProductPoints X X).filter fun p => dist p z ≤ r).card : ℝ) ≤
      (K*r^κ*(X.card : ℝ))^2 := by
    have hb := hcount.trans (mul_le_mul (hball (z 0)) (hball (z 1))
      (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _)))
    simpa only [pow_two] using hb
  exact nonnegative_bound_interpolation (Nat.cast_nonneg _)
    (scalarProductPoints_fine_ball hδ hr X hsep z) hweak hθ hθ1

theorem scalar_product_profile_factor {δ r K N κ θ : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hK : 0 ≤ K) (hN : 0 < N) :
    (81*(r/δ)^2)^θ*((K*r^κ*N)^2)^(1-θ) =
      (81^θ*K^(2*(1-θ))*(δ*N)^(-(2*θ)))*r^(2*θ+2*κ*(1-θ))*N^2 := by
  have hp (x e : ℝ) (hx : 0 ≤ x) : (x^2)^e = x^(2*e) := by
    simpa only [Real.rpow_ofNat] using (Real.rpow_mul hx 2 e).symm
  have ha : (81*(r/δ)^2)^θ = 81^θ*r^(2*θ)*δ^(-(2*θ)) := by
    rw [Real.mul_rpow (by norm_num) (sq_nonneg _),hp (r/δ) θ (div_nonneg hr.le hδ.le),
      Real.div_rpow hr.le hδ.le,div_eq_mul_inv,← Real.rpow_neg hδ.le]
    ring
  have hb : ((K*r^κ*N)^2)^(1-θ) = K^(2*(1-θ))*r^(κ*(2*(1-θ)))*N^(2*(1-θ)) := by
    rw [hp (K*r^κ*N) (1-θ) (by positivity),
      Real.mul_rpow (by positivity) hN.le,
      Real.mul_rpow hK (Real.rpow_nonneg hr.le _),← Real.rpow_mul hr.le]
  have hn : N^(2*(1-θ)) = N^(-(2*θ))*N^2 := by
    rw [← Real.rpow_natCast N 2,← Real.rpow_add hN]
    congr 1
    ring
  rw [ha,hb,hn]
  calc
    _ = (81^θ*K^(2*(1-θ)))*(δ^(-(2*θ))*N^(-(2*θ)))*
        (r^(2*θ)*r^(κ*(2*(1-θ))))*N^2 := by ring
    _ = _ := by
      rw [← Real.mul_rpow hδ.le hN.le,← Real.rpow_add hr]
      rw [show 2*θ+κ*(2*(1-θ)) = 2*θ+2*κ*(1-θ) by ring]

end Falconer

end OAI

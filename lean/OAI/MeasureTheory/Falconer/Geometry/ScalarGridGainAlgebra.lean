import OAI.MeasureTheory.Falconer.Geometry.ScalarGridProjection

namespace OAI

/-! Explicit scalar algebra for the uniform-direction gain. -/
namespace Falconer

 theorem product_potential_weight_mul {v A K θ : ℝ}
    (hv : 0 < v) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    max 1 (A*K^(2*(1-θ))*v^(-(2*θ)))*v ≤
      v+A*K^(2*(1-θ))*v^(1-2*θ) := by
  have hpos : 0 ≤ A*K^(2*(1-θ))*v^(-(2*θ)) := by positivity
  have hm : max 1 (A*K^(2*(1-θ))*v^(-(2*θ))) ≤
      1+A*K^(2*(1-θ))*v^(-(2*θ)) := max_le (by linarith) (by linarith)
  calc
    _ ≤ (1+A*K^(2*(1-θ))*v^(-(2*θ)))*v :=
      mul_le_mul_of_nonneg_right hm hv.le
    _ = v+A*K^(2*(1-θ))*v^(1-2*θ) := by
      rw [show 1-2*θ = -(2*θ)+1 by ring,Real.rpow_add hv,Real.rpow_one]
      ring

 theorem grid_projection_gain_of_rates {δ N M P θ ε : ℝ}
    (hδ : 0 < δ) (hN : 0 < N) (hP : 0 ≤ P)
    (hcount : 1/N ≤ δ^(2*ε)) (hvolume : δ*N ≤ δ^(2*ε))
    (hweight : (δ^(-ε))^(2*(1-θ))*(δ*N)^(1-2*θ) ≤ δ^(2*ε))
    (hsmall : (6+12*P*(1+81^θ))*δ^ε ≤ 1)
    (hproj : N^2/(1+(5+12*(max 1
      (81^θ*(δ^(-ε))^(2*(1-θ))*(δ*N)^(-(2*θ))))*P)*δ*N^2) ≤ M) :
    δ^(-ε)*N ≤ M := by
  let C := max 1 (81^θ*(δ^(-ε))^(2*(1-θ))*(δ*N)^(-(2*θ)))
  let D := 6+12*P*(1+81^θ)
  have hC : 0 ≤ C := (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _)
  have hden : 0 < 1+(5+12*C*P)*δ*N^2 := by positivity
  have hM : 0 ≤ M := (le_of_lt (div_pos (sq_pos_of_pos hN) hden)).trans hproj
  have hw := product_potential_weight_mul (θ := θ) (mul_pos hδ hN)
    (show (0 : ℝ) ≤ 81^θ by positivity) (show 0 ≤ δ^(-ε) by positivity)
  change C*(δ*N) ≤ δ*N+81^θ*(δ^(-ε))^(2*(1-θ))*(δ*N)^(1-2*θ) at hw
  have hw' : C*(δ*N) ≤ (1+81^θ)*δ^(2*ε) := by
    calc
      _ ≤ δ*N+81^θ*δ^(2*ε) := hw.trans (add_le_add le_rfl
        (by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hweight (show (0 : ℝ) ≤ 81^θ by positivity)))
      _ ≤ δ^(2*ε)+81^θ*δ^(2*ε) := add_le_add hvolume le_rfl
      _ = _ := by ring
  have hrate : 1/N+(5+12*C*P)*(δ*N) ≤ D*δ^(2*ε) := by
    have hv := mul_le_mul_of_nonneg_left hvolume (show (0 : ℝ) ≤ 5 by norm_num)
    have hc := mul_le_mul_of_nonneg_left hw' (show 0 ≤ 12*P by positivity)
    dsimp [D]
    nlinarith
  have hpow : D*δ^(2*ε) ≤ δ^ε := by
    have hh := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ δ^ε by positivity)
    calc
      _ = (D*δ^ε)*δ^ε := by
        rw [show 2*ε = ε+ε by ring,Real.rpow_add hδ]
        ring
      _ ≤ 1*δ^ε := hh
      _ = _ := one_mul _
  have hrate' := hrate.trans hpow
  have hnrate : 1+(5+12*C*P)*δ*N^2 ≤ δ^ε*N := by
    have hh := mul_le_mul_of_nonneg_right hrate' hN.le
    field_simp [hN.ne'] at hh
    nlinarith
  have hbase : N^2 ≤ M*(1+(5+12*C*P)*δ*N^2) := (div_le_iff₀ hden).1 hproj
  have hbase' := hbase.trans (mul_le_mul_of_nonneg_left hnrate hM)
  have hn : N ≤ M*δ^ε := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hn (show 0 ≤ δ^(-ε) by positivity)
  calc
    _ ≤ (M*δ^ε)*δ^(-ε) := by simpa only [mul_comm] using hh
    _ = M := by rw [mul_assoc,← Real.rpow_add hδ]; simp

end Falconer

end OAI

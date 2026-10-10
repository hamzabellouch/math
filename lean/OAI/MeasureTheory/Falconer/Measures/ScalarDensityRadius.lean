import OAI.MeasureTheory.Falconer.Measures.ScalarDensityZoom

namespace OAI

/-! Original weak ball bounds prevent the maximal-density interval from
collapsing to an uncontrolled radius. -/
namespace Falconer

 theorem scalar_density_radius_inequality {R θ K N m : ℝ}
    (hR : 0 < R) (hθ : 0 ≤ θ) (hK : 1 ≤ K) (hN : 0 < N)
    (hlower : N/(2:ℝ)^θ ≤ m/R^θ)
    (hupper : R ≤ 1 → m ≤ K*R^(2*θ)*N) :
    1 ≤ (2:ℝ)^θ*K*R^θ := by
  by_cases hR1 : R ≤ 1
  · have hp : 0 < R^θ := Real.rpow_pos_of_pos hR θ
    have htwo : 0 < (2:ℝ)^θ := by positivity
    have hl := (le_div_iff₀ hp).1 hlower
    have hl' := mul_le_mul_of_nonneg_left hl htwo.le
    have he : R^(2*θ) = (R^θ)^2 := by
      rw [show 2*θ = θ+θ by ring,Real.rpow_add hR,pow_two]
    have hu := hupper hR1
    rw [he] at hu
    have hu' := mul_le_mul_of_nonneg_left hu htwo.le
    have hlow : N*R^θ ≤ (2:ℝ)^θ*m := by
      have heq : (2:ℝ)^θ*(N/(2:ℝ)^θ*R^θ) = N*R^θ := by field_simp
      rwa [heq] at hl'
    have hh := hlow.trans hu'
    apply (mul_le_mul_iff_left₀ (mul_pos hN hp)).1
    convert hh using 1 <;> ring
  · have hp : 1 ≤ R^θ := Real.one_le_rpow (le_of_not_ge hR1) hθ
    have ht : 1 ≤ (2:ℝ)^θ := Real.one_le_rpow (by norm_num) hθ
    have hh : 1 ≤ (2:ℝ)^θ*K := by nlinarith
    nlinarith

 theorem scalar_density_radius_lower {R θ K : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hK : 0 < K)
    (hbound : 1 ≤ (2:ℝ)^θ*K*R^θ) :
    (1/((2:ℝ)^θ*K))^(1/θ) ≤ R := by
  have hC : 0 < (2:ℝ)^θ*K := by positivity
  have hh : 1/((2:ℝ)^θ*K) ≤ R^θ := (div_le_iff₀ hC).2 (by nlinarith)
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/((2:ℝ)^θ*K)) hh
    (by positivity : 0 ≤ 1/θ)
  have he : (R^θ)^(1/θ) = R := by
    rw [← Real.rpow_mul hR.le,mul_one_div_cancel hθ.ne',Real.rpow_one]
  rwa [he] at hp

end Falconer

end OAI

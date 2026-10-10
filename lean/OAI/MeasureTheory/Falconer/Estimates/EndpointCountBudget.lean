import OAI.MeasureTheory.Falconer.Slicing.GaussianLossAbsorption

namespace OAI

/-! # The strict dimension gap absorbs all endpoint tube-counting losses -/

namespace Falconer
open Real Filter
open scoped Topology

theorem endpoint_count_power {δ : ℝ} (hδ : 0 < δ) (C a κ s : ℝ) :
    (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 =
      ((6*C+35)^6*((6:ℝ)^s)^2)*δ^(2*s-3-6*a-5*κ) := by
  have hp (t : ℝ) (k : ℕ) : (δ^t)^k = δ^(t*(k:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
  rw [Real.mul_rpow (by norm_num) hδ.le,div_pow,mul_pow,mul_pow,
    hp (-1-κ) 3,hp a 6,hp (-κ) 2,hp s 2]
  calc
    _ = ((6*C+35)^6*((6:ℝ)^s)^2)*
        (δ^((-1-κ)*3)/δ^(a*6)*δ^(-κ*2)*δ^(s*2)) := by ring_nf
    _ = _ := by
      rw [← Real.rpow_sub hδ,← Real.rpow_add hδ,← Real.rpow_add hδ]
      congr 1
      ring_nf

theorem eventually_endpoint_count_budget {s a κ : ℝ}
    (hgap : 0 < 2*s-3-6*a-7*κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 < (δ^κ)^2 := by
  let K : ℝ := (6*C+35)^6*((6:ℝ)^s)^2
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show -(2*s-3-6*a-7*κ) < 0 by linarith)).eventually
    (eventually_gt_atTop K)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  rw [endpoint_count_power hδ.1]
  calc
    _ < δ^(-(2*s-3-6*a-7*κ))*δ^(2*s-3-6*a-5*κ) :=
      mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = (δ^κ)^2 := by
      rw [← Real.rpow_add hδ.1,← Real.rpow_natCast,← Real.rpow_mul hδ.1.le]
      congr 1
      ring_nf

end Falconer

end OAI

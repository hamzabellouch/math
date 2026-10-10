import OAI.Probability.SLE.Geometry.ExteriorFirstCoefficient
import OAI.Probability.SLE.Geometry.RootExteriorFlux

namespace OAI

/-! The area estimate controls the derivative of the normalized root
factor appearing in the odd-root transform. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma root_factor_derivative_le_one {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) (hq0 : q 0=1)
    (hne : ∀ z∈ball (0:ℂ) 1, q z≠0)
    (hi : InjOn (fun z : ℂ => z*q (z^2)) (ball 0 1)) :
    ‖deriv q 0‖≤1 := by
  obtain ⟨b,hb,hb0,he,_⟩ := root_exterior_laurent_data hq hq0 hne
  let C (w : ℂ) := w*b (w^2)
  have hs (w : ℂ) (hw : w∈ball (0:ℂ) 1) : w^2∈ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hw) (by norm_num)
  have hC : DifferentiableOn ℂ C (ball 0 1) :=
    differentiableOn_id.mul (hb.comp (differentiable_id.pow 2).differentiableOn hs)
  have hCd : deriv C 0=b 0 := by
    have hbD : HasDerivAt b (deriv b 0) ((0:ℂ)^2) := by
      simpa only [zero_pow (by norm_num : (2:ℕ)≠0)] using
        (hb.differentiableAt (ball_mem_nhds (0:ℂ) zero_lt_one)).hasDerivAt
    have hd := (hasDerivAt_id (0:ℂ)).mul
      (hbD.comp (0:ℂ) (hasDerivAt_pow 2 (0:ℂ)))
    change HasDerivAt C _ (0:ℂ) at hd
    simpa only [Function.comp_apply,id_eq,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_mul,
      add_zero,one_mul] using hd.deriv
  have hf := (root_exterior_univalent hq hne hi).1
  have hval (z : ℂ) (hz : 1<‖z‖) : rootExteriorChart q z=z+C z⁻¹ :=
    he z (norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hz)))
  have hh := exterior_first_coefficient_le_one hf hC hval
    (fun r hr => root_exterior_flux_nonneg hq hne hi hr)
  simpa only [hCd,hb0,norm_neg] using hh

end SLEExactGauge

end

end OAI

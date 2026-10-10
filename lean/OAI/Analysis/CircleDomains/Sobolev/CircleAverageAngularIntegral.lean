import OAI.Analysis.CircleDomains.Sobolev.ExteriorAngularEnergy

namespace OAI

/-! The nonnegative angular integral of a continuous circle function,
with exactly the polar chart's angular interval. -/
open Set Filter Function Metric Real MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma circleAverage_angular_lintegral {q : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hq : ContinuousOn q (sphere 0 r)) (hn : ∀ z ∈ sphere 0 r, 0 ≤ q z) :
    ENNReal.ofReal (2*Real.pi*circleAverage q 0 r) =
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (q (circleMap 0 r θ)) := by
  let g : ℝ → ℝ := fun θ => q (circleMap 0 r θ)
  have hmem (θ : ℝ) : circleMap 0 r θ ∈ sphere (0 : ℂ) r := by
    simpa only [abs_of_pos hr] using circleMap_mem_sphere' (0 : ℂ) r θ
  have hc : Continuous g := hq.comp_continuous (continuous_circleMap 0 r) hmem
  have hi : IntegrableOn g (Ioo (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])).mp
      (hc.intervalIntegrable _ _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun θ => hn _ (hmem θ)))]
  congr 1
  have hp : Periodic g (2*Real.pi) := by
    intro θ
    dsimp only [g]
    rw [periodic_circleMap 0 r θ]
  have he := hp.intervalIntegral_add_eq (-Real.pi) 0
  have ha : -Real.pi+2*Real.pi = Real.pi := by ring
  rw [ha, zero_add, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo] at he
  rw [he]
  change 2*Real.pi*((2*Real.pi)⁻¹*(∫ θ in (0 : ℝ)..2*Real.pi, g θ)) = _
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity : 2*Real.pi ≠ 0), one_mul]

end CircleDomainRigidity

end

end OAI

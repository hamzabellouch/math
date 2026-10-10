import Mathlib
import OAI.Analysis.AffineBernstein.AffineInvariantCap

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- Original-PDE cap bound for the nonnegative integral used by actual chart transport.
Integrability is produced from the compact cap data, not added as a hypothesis. -/
theorem affineMaximal_uniform_affine_cap_lintegral_bound (n : ℕ)
    {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R)
    (t₀ t₁ q₀ : ℝ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      ∀ (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
        (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ),
      Metric.closedBall (L (o,c)+v) r ⊆ (fun p => L p+v) '' sourceEpigraph Ω u →
      a o+b*c+d = q₀ →
      ∀ {K Q : Set (Space n)}, IsCompact K → K ⊆ Ω → MeasurableSet Q → Q ⊆ K →
      (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ graphAffineFunction u a b d x) →
      (∀ x ∈ K, graphAffineFunction u a b d x ∈ Icc t₀ (t₁+ε)) →
      (∀ x ∈ Q, graphAffineFunction u a b d x ≤ t₁-ε) →
      (∀ x ∈ K, ∀ j, |(L (x,u x)+v).1 j| ≤ R) →
      (∀ x ∈ K, |(L (x,u x)+v).2| ≤ R) →
      ENNReal.ofReal (Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))) *
        (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
          (‖affineGraphConormal u L x‖ * graphInverseMetric u a b d x))) ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := affineMaximal_uniform_affine_cap_bound n hε hr hR t₀ t₁ q₀
  refine ⟨C,hC,?_⟩
  intro Ω hΩ hcv u hu hp hm L v o c a b d hball hq₀ K Q hK hKΩ hQ hQK hs hqK hqQ hxR htR
  have hAc : ContinuousOn (affineAreaDensity u) K := fun x hx =>
    (contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx))).continuousAt.continuousWithinAt
  have hNc : ContinuousOn (fun x => ‖affineGraphConormal u L x‖) K := fun x hx =>
    (continuousAt_affineGraphConormal (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))) L).norm.continuousWithinAt
  have hVc : ContinuousOn (graphInverseMetric u a b d) K := fun x hx =>
    (contDiffAt_graphInverseMetric (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx)) a b d).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun x => affineAreaDensity u x *
      (‖affineGraphConormal u L x‖ * graphInverseMetric u a b d x)) Q :=
    ((hAc.mul (hNc.mul hVc)).integrableOn_compact hK).mono_set hQK
  have hnn : 0 ≤ᵐ[volume.restrict Q] (fun x => affineAreaDensity u x *
      (‖affineGraphConormal u L x‖ * graphInverseMetric u a b d x)) := by
    filter_upwards [ae_restrict_mem hQ] with x hx
    exact mul_nonneg (Real.rpow_nonneg (hp x (hKΩ (hQK hx))).det_pos.le _)
      (mul_nonneg (norm_nonneg _) (graphInverseMetric_nonneg (hp x (hKΩ (hQK hx))) a b d))
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  rw [← ENNReal.ofReal_mul (p := Real.rpow |L.toContinuousLinearMap.det|
    ((n:ℝ)/((n:ℝ)+2))) (Real.rpow_nonneg (abs_nonneg _) _)]
  exact ENNReal.ofReal_le_ofReal (hbound hΩ hcv hu hp hm L v o c a b d hball hq₀
    hK hKΩ hQ hQK hs hqK hqQ hxR htR)

end AffineBernstein
end

end OAI

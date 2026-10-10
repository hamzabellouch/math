import OAI.Probability.SLE.Gauge.CanonicalDiskMomentTails

namespace OAI

/-! The prescribed finite batch level supplies the successful-test budget.
This uses its exact retained moment and the next limiting moment bound. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem centeredDiskLaw_batch_success
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    {n : ℕ} (hn : 3≤n) :
    (2:ℝ)^n/8 ≤ ∑' k : ℤ, (Target.multiplicity κ W n k : ℝ) *
      (centeredDiskLaw P κ B hc (4*(Target.batchLevel κ W n:ℝ)/κ)).real
        {p | MomentBatches.dyadic k ≤ C.diskAtRadius p.1 (4*(Target.batchLevel κ W n:ℝ)/κ) p.2} := by
  let ℓ := Target.batchLevel κ W n
  have hu : 0≤4*(ℓ:ℝ)/κ := div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg ℓ)) hκ.le
  let := centeredDiskLaw_isProbability hB hBm hc hκ hκ8 γ G F hw _ hu
  apply MomentBatches.target_lower_batch_probability
    (centeredDiskLaw P κ B hc (4*(ℓ:ℝ)/κ))
    (fun p => C.diskAtRadius p.1 (4*(ℓ:ℝ)/κ) p.2)
    (C.diskAtRadius_joint_measurable hc F hw _ hu)
    (fun p => C.diskAtRadius_nonneg _ _ _) κ W hn
    (C.moment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW n)
    (C.moment_positive hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW (n+1))
    (C.centeredDiskLaw_integrable_pow hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ (Nat.cast_nonneg ℓ) n)
    (C.centeredDiskLaw_integrable_pow hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ (Nat.cast_nonneg ℓ) (n+1))
  · rw [C.centeredDiskLaw_integral_pow hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ (Nat.cast_nonneg ℓ) n]
    exact (C.prescribed_batch_retains_moment hB hc h0 hκ hκ8 F hw hpublished hgrowth W hW n).2.le
  · rw [C.centeredDiskLaw_integral_pow hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ (Nat.cast_nonneg ℓ) (n+1)]
    exact C.finiteMoment_nat_le_moment hB hc h0 hκ hκ8 F hw hgrowth W hW (n+1) ℓ

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

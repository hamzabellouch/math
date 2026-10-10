import OAI.Probability.SLE.Geometry.CanonicalDiskPotential
import OAI.Probability.SLE.Angle.TargetNormalizedFiltration
import OAI.Probability.SLE.Angle.TargetLevelTime

namespace OAI

/-! Canonical remaining mass in the exact clock and natural filtration
of the source-prescribed Brownian driver. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem normalized_potential_condExp [IsProbabilityMeasure P]
    (hκ : 0<κ) (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (t : ℝ≥0) :
    (fun ω => (Target.potential κ θ (Target.normalizedDriver κ B hc h0 ω) t).toReal) =ᵐ[P]
      P[C.diskTerminalScalar θ hθ-C.diskScalar θ hθ (t/κ.toNNReal) |
        Target.normalizedFiltration κ B
          (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0 t] := by
  have ht : κ*((t/κ.toNNReal:ℝ≥0):ℝ)=(t:ℝ) := by
    rw [NNReal.coe_div,Real.coe_toNNReal _ hκ.le,mul_div_cancel₀ _ hκ.ne']
  erw [Target.normalizedFiltration_at κ hκ B
    (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0 t]
  simpa only [ht] using C.target_potential_condExp hκ hc F hw
    (Target.normalizedDriver κ B hc h0) (Target.normalizedDriver_matches κ hκ B hc h0)
    θ hθ (t/κ.toNNReal)

include hBm in
theorem normalized_potential_lintegral_ne_top
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (t : ℝ≥0) :
    (∫⁻ ω, Target.potential κ θ (Target.normalizedDriver κ B hc h0 ω) t ∂P) ≠ ∞ := by
  have ht : κ*((t/κ.toNNReal:ℝ≥0):ℝ)=(t:ℝ) := by
    rw [NNReal.coe_div,Real.coe_toNNReal _ hκ.le,mul_div_cancel₀ _ hκ.ne']
  simpa only [ht] using target_potential_lintegral_ne_top (hBm := hBm)
    hB hκ hκ8 hc h0 F hw (Target.normalizedDriver κ B hc h0)
    (Target.normalizedDriver_matches κ hκ B hc h0) θ hθ (t/κ.toNNReal)

include hBm in
theorem normalized_levelTime_measurable
    (hκ : 0<κ) (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (θ ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    Measurable (fun ω => Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ) := by
  apply Target.measurable_levelTime_of_radius_kernel κ hκ _ _
    (fun ω => (hc ω).const_mul _) γ G F hw
    (Target.normalizedDriver_matches κ hκ B hc h0) θ ℓ hℓ
  have hu : 0 ≤ 4*ℓ/κ := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  have hm := measurable_canonicalRadiusLevel_random_state κ
    (source_path_measurable (sourceDriverPath B hc)
      (fun t => hBm.comp (measurable_const.prodMk measurable_id)))
    (u := fun _ => 4*ℓ/κ) measurable_const
    (z := fun _ => Target.diskMapInv θ 0) measurable_const
  convert hm using 1
  funext ω
  exact (canonicalRadiusLevel_eq κ (sourceDriverPath B hc ω) (hw ω) _ hu _).symm

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

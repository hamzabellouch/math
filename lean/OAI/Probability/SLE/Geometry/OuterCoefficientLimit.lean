import OAI.Probability.SLE.Stochastic.WienerCoefficientLimit
import OAI.Probability.SLE.Loewner.TargetOuterMeasurability

namespace OAI

/-! The bounded clipping permits the mesh limit to pass through the exact
invariant-angle integral without an estimate uniform in the angle. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

def clippedCoefficient (κ : ℝ) (W : WienerLaw) (ℓ u : ℝ) (k : ℕ) (θ : ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ => ∫ b, levelDensity κ θ b ℓ *
    (clip u (discreteMass κ θ W b ℓ n))^k ∂W)

end SLEExactGauge.Target

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

include C in
theorem clippedCoefficient_tendsto
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    Tendsto (fun n => ∫ b, Target.levelDensity κ θ b ℓ *
      (Target.clip u (Target.discreteMass κ θ W b ℓ n))^k ∂W) atTop
      (𝓝 (Target.clippedCoefficient κ W ℓ u k θ)) := by
  have h := C.wiener_clipped_coefficient_limit hB hκ hκ8 hc h0 F hw W hW θ hθ ℓ hℓ u hu k
  simpa only [Target.clippedCoefficient,h.limUnder_eq] using h

theorem clippedCoefficient_eq_mass
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    Target.clippedCoefficient κ W ℓ u k θ =
      ∫ ω, Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ *
        (Target.clip u (massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
          (C.diskTerminalScalar θ hθ ω)
          (Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ)))^k ∂P :=
  (C.wiener_clipped_coefficient_limit hB hκ hκ8 hc h0 F hw W hW θ hθ ℓ hℓ u hu k).limUnder_eq

include C in
theorem outer_clipped_coefficient_limit
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    Tendsto (fun n => ∫ θ, ∫ b, Target.levelDensity κ θ b ℓ *
      (Target.clip u (Target.discreteMass κ θ W b ℓ n))^k ∂W ∂Target.angleLaw κ) atTop
      (𝓝 (∫ θ, Target.clippedCoefficient κ W ℓ u k θ ∂Target.angleLaw κ)) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let : IsProbabilityMeasure (Target.angleLaw κ) := Target.angleLaw_isProbability hκ
  apply tendsto_integral_of_dominated_convergence (fun _ => u^k)
  · intro n
    exact (Target.aemeasurable_coefficient_integrand κ ℓ u W n k).aestronglyMeasurable.integral_prod_right'
  · exact integrable_const _
  · intro n
    filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
    have hb := wiener_clipped_coefficient_bound (hBm := hBm) hB hκ hκ8 hc h0 F hw W hW θ hθ ℓ hℓ u hu n k
    rw [Real.norm_of_nonneg hb.1]
    exact hb.2
  · filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
    exact C.clippedCoefficient_tendsto hB hκ hκ8 hc h0 F hw W hW θ hθ ℓ hℓ u hu k

include C in
theorem finiteMoment_eq_outer_clipped_limit
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (k : ℕ) :
    Target.finiteMoment κ W k ℓ = limUnder atTop (fun u : ℕ =>
      ∫ θ, Target.clippedCoefficient κ W ℓ u k θ ∂Target.angleLaw κ) := by
  unfold Target.finiteMoment
  congr 1
  funext u
  exact (C.outer_clipped_coefficient_limit hB hκ hκ8 hc h0 F hw W hW ℓ hℓ u
    (Nat.cast_nonneg u) k).limUnder_eq

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

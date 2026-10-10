import OAI.Probability.SLE.Geometry.CoefficientAngularBound

namespace OAI

/-! The paper's iterated finite-level coefficient equals the invariant
angle average of the actual stopped canonical disk moment. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

def levelCoefficient (κ : ℝ) (W : WienerLaw) (ℓ : ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ => clippedCoefficient κ W ℓ n m θ)

end SLEExactGauge.Target

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

include C in
lemma clippedCoefficient_aestronglyMeasurable
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (ℓ : ℝ) (hℓ : 0≤ℓ) (u : ℝ) (hu : 0≤u) (m : ℕ) :
    AEStronglyMeasurable (Target.clippedCoefficient κ W ℓ u m) (Target.angleLaw κ) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (Target.aemeasurable_coefficient_integrand κ ℓ u W n m).aestronglyMeasurable.integral_prod_right')
  filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
  exact C.clippedCoefficient_tendsto hB hκ hκ8 hc h0 F hw W hW θ hθ ℓ hℓ u hu m

include C in
lemma levelCoefficient_tendsto
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    Tendsto (fun n : ℕ => Target.clippedCoefficient κ W ℓ n m θ) atTop
      (𝓝 (Target.levelCoefficient κ W ℓ m θ)) := by
  have h := C.clippedCoefficient_unclip_limit hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m
  simpa only [Target.levelCoefficient,h.limUnder_eq] using h

lemma levelCoefficient_eq_mass
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    Target.levelCoefficient κ W ℓ m θ =
      ∫ ω, Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ *
        (massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
          (C.diskTerminalScalar θ hθ ω)
          (Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ))^m ∂P :=
  (C.clippedCoefficient_unclip_limit hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m).limUnder_eq

include C in
theorem finiteMoment_eq_levelCoefficientIntegral
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    Target.finiteMoment κ W m ℓ =
      ∫ θ, Target.levelCoefficient κ W ℓ m θ ∂Target.angleLaw κ := by
  obtain ⟨M,hM,hbound⟩ := C.uniform_clippedCoefficient_bound hB hc h0 hκ hκ8 F hw hgrowth W hW m
  have hi : Integrable (fun θ => M/(Real.sin θ)^greenExponent κ) (Target.angleLaw κ) := by
    simpa only [div_eq_mul_inv,mul_one,one_mul] using (Target.angle_inverse_sine_integrable κ).const_mul M
  have ht : Tendsto (fun n : ℕ => ∫ θ, Target.clippedCoefficient κ W ℓ n m θ ∂Target.angleLaw κ)
      atTop (𝓝 (∫ θ, Target.levelCoefficient κ W ℓ m θ ∂Target.angleLaw κ)) := by
    apply tendsto_integral_of_dominated_convergence (fun θ => M/(Real.sin θ)^greenExponent κ)
    · intro n
      exact C.clippedCoefficient_aestronglyMeasurable hB hc h0 hκ hκ8 F hw W hW ℓ hℓ n (Nat.cast_nonneg n) m
    · exact hi
    · intro n
      filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
      have hb := hbound θ hθ ℓ hℓ n (Nat.cast_nonneg n)
      rw [Real.norm_of_nonneg hb.1]
      exact hb.2
    · filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
      exact C.levelCoefficient_tendsto hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m
  rw [C.finiteMoment_eq_outer_clipped_limit hB hκ hκ8 hc h0 F hw W hW ℓ hℓ m]
  exact ht.limUnder_eq

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

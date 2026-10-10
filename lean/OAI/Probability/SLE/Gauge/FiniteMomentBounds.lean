import OAI.Probability.SLE.Gauge.FiniteMomentIdentification

namespace OAI

/-! Finite and uniformly bounded prescribed finite-level moments. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

include C in
lemma levelCoefficient_aestronglyMeasurable
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    AEStronglyMeasurable (Target.levelCoefficient κ W ℓ m) (Target.angleLaw κ) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n : ℕ => C.clippedCoefficient_aestronglyMeasurable hB hc h0 hκ hκ8 F hw W hW
      ℓ hℓ n (Nat.cast_nonneg n) m)
  filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
  exact C.levelCoefficient_tendsto hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m

include C in
theorem uniform_finiteMoment_bound
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W) (m : ℕ) :
    ∃ M : ℝ, 0≤M ∧ ∀ ℓ : ℝ, 0≤ℓ → 0≤Target.finiteMoment κ W m ℓ ∧
      Target.finiteMoment κ W m ℓ≤M := by
  obtain ⟨M,hM,hbound⟩ := C.uniform_clippedCoefficient_bound hB hc h0 hκ hκ8 F hw hgrowth W hW m
  let g := fun θ => M/(Real.sin θ)^greenExponent κ
  have hg : Integrable g (Target.angleLaw κ) := by
    simpa only [g,div_eq_mul_inv,mul_one,one_mul] using (Target.angle_inverse_sine_integrable κ).const_mul M
  have hg0 : 0≤ᵐ[Target.angleLaw κ] g := by
    filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
    exact div_nonneg hM (Real.rpow_nonneg (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le _)
  refine ⟨∫ θ, g θ ∂Target.angleLaw κ,integral_nonneg_of_ae hg0,?_⟩
  intro ℓ hℓ
  have hlim := C.levelCoefficient_tendsto hB hc h0 hκ hκ8 F hw hgrowth W hW
  have hb : ∀ᵐ θ ∂Target.angleLaw κ, 0≤Target.levelCoefficient κ W ℓ m θ ∧
      Target.levelCoefficient κ W ℓ m θ≤g θ := by
    filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
    have ht := hlim θ hθ ℓ hℓ m
    exact ⟨ge_of_tendsto ht (Eventually.of_forall (fun n =>
      (hbound θ hθ ℓ hℓ n (Nat.cast_nonneg n)).1)),
      le_of_tendsto ht (Eventually.of_forall (fun n =>
      (hbound θ hθ ℓ hℓ n (Nat.cast_nonneg n)).2))⟩
  have hi : Integrable (Target.levelCoefficient κ W ℓ m) (Target.angleLaw κ) := by
    apply hg.mono' (C.levelCoefficient_aestronglyMeasurable hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m)
    filter_upwards [hb] with θ hθ
    rw [Real.norm_of_nonneg hθ.1]
    exact hθ.2
  rw [C.finiteMoment_eq_levelCoefficientIntegral hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m]
  exact ⟨integral_nonneg_of_ae (hb.mono (fun _ h => h.1)),
    integral_mono_ae hi hg (hb.mono (fun _ h => h.2))⟩

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

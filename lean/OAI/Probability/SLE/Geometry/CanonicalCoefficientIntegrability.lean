import OAI.Probability.SLE.Gauge.DensityWeightedMoments
import OAI.Probability.SLE.Geometry.NormalizedStoppedDisk
import OAI.Probability.SLE.Geometry.OuterCoefficientLimit
import OAI.Probability.SLE.Gauge.MomentUnclipping

namespace OAI

/-! Integrability and removal of the exact coefficient's clipping,
using the canonical terminal disk moment as a dominator. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma density_disk_terminal_integrable
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (m : ℕ)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ) :
    Integrable (fun ω => Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ *
      (C.diskTerminalScalar θ hθ ω)^m) P := by
  obtain ⟨M,hM,hbound⟩ := C.uniform_density_disk_terminal_moments hB hc h0 hκ hκ8 F hw hgrowth m
  have hb := Target.normalizedDriver_measurable κ B
    (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0
  have hwM := (Target.measurable_fixedLevelDensity κ θ ℓ).comp hb
  have hzM : Measurable (C.diskTerminalScalar θ hθ) := (compactWeightedMass_measurable _ _ (Target.diskSourceHalfPlane_compact hθ).measurableSet).comp
    C.rational.terminal_measurable
  have hnonneg (ω) : 0≤Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ *
      (C.diskTerminalScalar θ hθ ω)^m :=
    mul_nonneg (Target.levelDensity_nonneg_of_witness κ hκ _ _ ((hc ω).const_mul _)
      (γ ω) (G ω) (F ω) (hw ω) (Target.normalizedDriver_matches κ hκ B hc h0 ω) θ hθ ℓ hℓ)
      (pow_nonneg (compactWeightedMass_nonneg _ _ _) m)
  apply (lintegral_ofReal_ne_top_iff_integrable (hwM.mul (hzM.pow_const m)).aestronglyMeasurable
    (Eventually.of_forall hnonneg)).mp
  exact ne_top_of_lt ((hbound θ hθ ℓ hℓ).trans_lt (ENNReal.mul_lt_top hM ENNReal.ofReal_lt_top))

theorem clippedCoefficient_unclip_limit [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    Tendsto (fun n : ℕ => Target.clippedCoefficient κ W ℓ n m θ) atTop
      (𝓝 (∫ ω, Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ *
        (massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
          (C.diskTerminalScalar θ hθ ω)
          (Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ))^m ∂P)) := by
  let T := fun ω => Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ
  let Y := fun ω => massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
    (C.diskTerminalScalar θ hθ ω) (T ω)
  let w := fun ω => Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ
  have hT : Measurable T := normalized_levelTime_measurable (hBm:=hBm) hκ hc h0 F hw θ ℓ hℓ
  have hY : Measurable Y := C.normalizedStoppedDisk_measurable θ hθ T hT
  have hwM : Measurable w := (Target.measurable_fixedLevelDensity κ θ ℓ).comp
    (Target.normalizedDriver_measurable κ B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0)
  have hd : ∀ᵐ ω ∂P, 0≤w ω ∧ 0≤Y ω ∧ Y ω≤C.diskTerminalScalar θ hθ ω := by
    filter_upwards [C.normalizedStoppedDisk_le_terminal hκ θ hθ T] with ω hω
    exact ⟨Target.levelDensity_nonneg_of_witness κ hκ _ _ ((hc ω).const_mul _)
      (γ ω) (G ω) (F ω) (hw ω) (Target.normalizedDriver_matches κ hκ B hc h0 ω) θ hθ ℓ hℓ,
      C.normalizedStoppedDisk_nonneg θ hθ (T ω) ω,hω⟩
  have ht := weighted_unclip_pow_tendsto P Y (C.diskTerminalScalar θ hθ) w
    hY.aestronglyMeasurable hwM.aestronglyMeasurable hd m
    (C.density_disk_terminal_integrable hB hc h0 hκ hκ8 F hw hgrowth m θ hθ ℓ hℓ)
  apply ht.congr'
  filter_upwards [] with n
  exact (C.clippedCoefficient_eq_mass hB hκ hκ8 hc h0 F hw W hW θ hθ ℓ hℓ n (Nat.cast_nonneg n) m).symm

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

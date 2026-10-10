import OAI.Probability.SLE.Geometry.NormalizedCoefficientLimit
import OAI.Probability.SLE.Angle.TargetLevelMeasurability

namespace OAI

/-! Transfer of the exact fixed-angle coefficient limit to the Wiener
integrals appearing in the prescribed deterministic gauge. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma measurable_fixedLevelDensity (κ θ ℓ : ℝ) :
    Measurable (fun b => levelDensity κ θ b ℓ) :=
  @Measurable.comp Driver (ℝ × Driver) ℝ
    inferInstance inferInstance inferInstance
    (fun p => levelDensity κ p.1 p.2 ℓ) (fun b => (θ,b))
    (measurable_levelDensity_angle κ ℓ) (measurable_const.prodMk measurable_id)

lemma measurable_fixedDiscreteMass (κ θ : ℝ) (W : WienerLaw) [SFinite W] (ℓ : ℝ) (n : ℕ) :
    Measurable (fun b => discreteMass κ θ W b ℓ n) := by
  have ht : Measurable (fun b : Driver => levelTime κ θ b ℓ) :=
    @Measurable.comp Driver (ℝ × Driver) ℝ≥0∞
      inferInstance inferInstance inferInstance
      (fun p => levelTime κ p.1 p.2 ℓ) (fun b => (θ,b))
      (measurable_levelTime_angle κ ℓ) (measurable_const.prodMk measurable_id)
  exact discreteMass_comp_measurable κ θ W id measurable_id ℓ ht n

lemma measurable_fixedCoefficient (κ θ : ℝ) (W : WienerLaw) [SFinite W]
    (ℓ u : ℝ) (n k : ℕ) :
    Measurable (fun b => levelDensity κ θ b ℓ*(clip u (discreteMass κ θ W b ℓ n))^k) :=
  (measurable_fixedLevelDensity κ θ ℓ).mul
    (((continuous_clip u).measurable.comp (measurable_fixedDiscreteMass κ θ W ℓ n)).pow_const k)

lemma levelDensity_nonneg_of_witness
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ) (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    0 ≤ levelDensity κ θ b ℓ := by
  rw [levelDensity_eq_stoppedGreen κ hκ b U hUc γ G F hw hU θ hθ ℓ hℓ]
  exact div_nonneg (stoppedGreen_nonneg hw κ _ _)
    (initialGreen_pos κ _ (diskMapInv_maps hθ (by simp))).le

end SLEExactGauge.Target

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem wiener_clipped_coefficient_limit
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    Tendsto (fun n => ∫ b, Target.levelDensity κ θ b ℓ *
      (Target.clip u (Target.discreteMass κ θ W b ℓ n))^k ∂W) atTop
      (𝓝 (∫ ω, Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ *
        (Target.clip u (massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
          (C.diskTerminalScalar θ hθ ω)
          (Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ)))^k ∂P)) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hLaw := Target.normalizedDriver_law κ hκ B hB
    (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0 W hW
  have he (n : ℕ) := hLaw.integral_comp
    (Target.measurable_fixedCoefficient κ θ W ℓ u n k).aestronglyMeasurable
  have ht := C.normalized_clipped_coefficient_limit hB hκ hκ8 hc h0 F hw W hW θ hθ ℓ hℓ u hu k
  apply ht.congr'
  filter_upwards [] with n
  exact he n

include hBm in
theorem wiener_clipped_coefficient_bound
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (u : ℝ) (hu : 0 ≤ u) (n k : ℕ) :
    0 ≤ (∫ b, Target.levelDensity κ θ b ℓ *
      (Target.clip u (Target.discreteMass κ θ W b ℓ n))^k ∂W) ∧
    (∫ b, Target.levelDensity κ θ b ℓ *
      (Target.clip u (Target.discreteMass κ θ W b ℓ n))^k ∂W) ≤ u^k := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let b := Target.normalizedDriver κ B hc h0
  let w := fun ω => Target.levelDensity κ θ (b ω) ℓ
  let f := fun ω => (Target.clip u (Target.discreteMass κ θ W (b ω) ℓ n))^k
  have hm (r : ℝ≥0) : Measurable (B r) := hBm.comp (measurable_const.prodMk measurable_id)
  have hb := Target.normalizedDriver_measurable κ B hm hc h0
  have hLaw := Target.normalizedDriver_law κ hκ B hB hm hc h0 W hW
  have he := hLaw.integral_comp
    (Target.measurable_fixedCoefficient κ θ W ℓ u n k).aestronglyMeasurable
  rw [← he]
  change 0 ≤ (∫ ω, w ω*f ω ∂P) ∧ (∫ ω, w ω*f ω ∂P) ≤ u^k
  have hwi := Target.levelDensity_integrable_mean κ hκ hκ8 B hB b γ G F
    (Eventually.of_forall hw) (Eventually.of_forall (Target.normalizedDriver_matches κ hκ B hc h0))
    θ hθ ℓ hℓ
  have hw0 (ω : Ω) : 0 ≤ w ω := Target.levelDensity_nonneg_of_witness κ hκ (b ω) _
    ((hc ω).const_mul _) (γ ω) (G ω) (F ω) (hw ω)
    (Target.normalizedDriver_matches κ hκ B hc h0 ω) θ hθ ℓ hℓ
  have hf0 (ω : Ω) : 0 ≤ f ω := pow_nonneg (clip_nonneg hu _) k
  have hfb (ω : Ω) : f ω ≤ u^k :=
    pow_le_pow_left₀ (clip_nonneg hu _) (clip_le _ _) k
  have hprod : Integrable (fun ω => w ω*f ω) P := by
    apply (hwi.1.norm.mul_const (u^k)).mono'
      ((Target.measurable_fixedCoefficient κ θ W ℓ u n k).comp hb).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖w ω * f ω‖ ≤ ‖w ω‖ * u^k
    rw [norm_mul,Real.norm_of_nonneg (hf0 ω)]
    exact mul_le_mul_of_nonneg_left (hfb ω) (norm_nonneg _)
  refine ⟨integral_nonneg (fun ω => mul_nonneg (hw0 ω) (hf0 ω)),?_⟩
  calc
    (∫ ω, w ω*f ω ∂P) ≤ ∫ ω, w ω*u^k ∂P :=
      integral_mono hprod (hwi.1.mul_const _) (fun ω => mul_le_mul_of_nonneg_left (hfb ω) (hw0 ω))
    _ = u^k := by rw [integral_mul_const,hwi.2,one_mul]

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

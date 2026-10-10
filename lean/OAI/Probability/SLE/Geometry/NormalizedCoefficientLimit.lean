import OAI.Probability.SLE.Geometry.NormalizedPotentialIncrement
import OAI.Probability.SLE.Angle.TargetLevelDensity

namespace OAI

/-! The inner mesh limit in the prescribed coefficient is the clipped
moment of the actual canonical disk mass at the prescribed level. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma measurable_potentialDifference (κ θ : ℝ) (W : WienerLaw) [SFinite W] (n i : ℕ) :
    Measurable (fun b => potentialDifference κ θ W b n i) := by
  have hv := measurable_potential κ θ (compensatorMeshTime n i)
  have hw := measurable_continuationMean W (compensatorMeshTime n i)
    (fun b => potential κ θ b (compensatorMeshTime n (i+1)))
    (measurable_potential κ θ (compensatorMeshTime n (i+1)))
  have hn : ((i:ℝ)+1)*mesh n=(compensatorMeshTime n (i+1):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using mesh_eq_compensatorMeshTime n (i+1)
  simp only [potentialDifference,mesh_eq_compensatorMeshTime,hn]
  exact (hv.ennreal_toReal.sub hw.ennreal_toReal).ite
    ((measurableSet_lt hv measurable_const).inter (measurableSet_lt hw measurable_const))
    measurable_const

lemma discreteMass_comp_measurable
    {Ω : Type*} [MeasurableSpace Ω] (κ θ : ℝ) (W : WienerLaw) [SFinite W]
    (b : Ω → Driver) (hb : Measurable b) (ℓ : ℝ)
    (hT : Measurable (fun ω => levelTime κ θ (b ω) ℓ)) (n : ℕ) :
    Measurable (fun ω => discreteMass κ θ W (b ω) ℓ n) := by
  unfold discreteMass
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_potentialDifference κ θ W n i).comp hb).ite
    (measurableSet_le measurable_const hT) measurable_const

end SLEExactGauge.Target

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem normalized_clipped_coefficient_limit
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    Tendsto (fun n => ∫ ω, Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ *
      (Target.clip u (Target.discreteMass κ θ W (Target.normalizedDriver κ B hc h0 ω) ℓ n))^k ∂P)
      atTop (𝓝 (∫ ω, Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ *
        (Target.clip u (massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
          (C.diskTerminalScalar θ hθ ω)
          (Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ)))^k ∂P)) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  apply weighted_clip_pow_integral_tendsto P _ _ _ _ _
    (C.normalized_discreteMass_tendstoInMeasure hB hκ hκ8 hc h0 F hw W hW θ hθ ℓ hℓ)
    u hu k
  · intro n
    exact (Target.discreteMass_comp_measurable κ θ W _
      (Target.normalizedDriver_measurable κ B
        (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0) ℓ
      (normalized_levelTime_measurable (hBm := hBm) hκ hc h0 F hw θ ℓ hℓ) n).aestronglyMeasurable
  · exact (Target.levelDensity_integrable_mean κ hκ hκ8 B hB
      (Target.normalizedDriver κ B hc h0) γ G F (Eventually.of_forall hw)
      (Eventually.of_forall (Target.normalizedDriver_matches κ hκ B hc h0)) θ hθ ℓ hℓ).1

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

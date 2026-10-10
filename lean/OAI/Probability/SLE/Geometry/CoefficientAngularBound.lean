import OAI.Probability.SLE.Geometry.CanonicalCoefficientIntegrability

namespace OAI

/-! One integrable angular majorant for every clipping and center level
in the exact Wiener coefficient formula. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

include C in
theorem uniform_clippedCoefficient_bound
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W) (m : ℕ) :
    ∃ M : ℝ, 0≤M ∧ ∀ θ∈Ioo (0:ℝ) Real.pi, ∀ ℓ : ℝ, 0≤ℓ → ∀ u : ℝ, 0≤u →
      0≤Target.clippedCoefficient κ W ℓ u m θ ∧
        Target.clippedCoefficient κ W ℓ u m θ≤M/(Real.sin θ)^greenExponent κ := by
  obtain ⟨M,hM,hbound⟩ := C.uniform_density_disk_terminal_moments hB hc h0 hκ hκ8 F hw hgrowth m
  refine ⟨M.toReal,ENNReal.toReal_nonneg,?_⟩
  intro θ hθ ℓ hℓ u hu
  let T := fun ω => Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ
  let Y := fun ω => massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
    (C.diskTerminalScalar θ hθ ω) (T ω)
  let w := fun ω => Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ
  have hT : Measurable T := normalized_levelTime_measurable (hBm:=hBm) hκ hc h0 F hw θ ℓ hℓ
  have hY : Measurable Y := C.normalizedStoppedDisk_measurable θ hθ T hT
  have hwM : Measurable w := (Target.measurable_fixedLevelDensity κ θ ℓ).comp
    (Target.normalizedDriver_measurable κ B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0)
  have hw0 (ω) : 0≤w ω := Target.levelDensity_nonneg_of_witness κ hκ _ _ ((hc ω).const_mul _)
    (γ ω) (G ω) (F ω) (hw ω) (Target.normalizedDriver_matches κ hκ B hc h0 ω) θ hθ ℓ hℓ
  have hd : ∀ᵐ ω ∂P, 0≤w ω ∧ 0≤Y ω ∧ Y ω≤C.diskTerminalScalar θ hθ ω := by
    filter_upwards [C.normalizedStoppedDisk_le_terminal hκ θ hθ T] with ω hω
    exact ⟨hw0 ω,C.normalizedStoppedDisk_nonneg θ hθ (T ω) ω,hω⟩
  have hi := C.density_disk_terminal_integrable hB hc h0 hκ hκ8 F hw hgrowth m θ hθ ℓ hℓ
  have hb := weighted_clip_integral_bound P Y (C.diskTerminalScalar θ hθ) w
    hY.aestronglyMeasurable hwM.aestronglyMeasurable hd m hi u hu
  rw [C.clippedCoefficient_eq_mass hB hκ hκ8 hc h0 F hw W hW θ hθ ℓ hℓ u hu m]
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hs : 0<Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hI0 : 0≤(∫ ω, w ω*(C.diskTerminalScalar θ hθ ω)^m ∂P) := integral_nonneg
    (fun ω => mul_nonneg (hw0 ω) (pow_nonneg (compactWeightedMass_nonneg _ _ _) m))
  have hEn : ENNReal.ofReal (∫ ω, w ω*(C.diskTerminalScalar θ hθ ω)^m ∂P) ≤
      M*ENNReal.ofReal (1/(Real.sin θ)^greenExponent κ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi]
    · exact hbound θ hθ ℓ hℓ
    · exact Eventually.of_forall (fun ω => mul_nonneg (hw0 ω)
        (pow_nonneg (compactWeightedMass_nonneg _ _ _) m))
  have ht := ENNReal.toReal_mono
    (ne_top_of_lt (ENNReal.mul_lt_top hM ENNReal.ofReal_lt_top)) hEn
  rw [ENNReal.toReal_ofReal hI0,ENNReal.toReal_mul,ENNReal.toReal_ofReal
    (one_div_nonneg.mpr (Real.rpow_nonneg hs.le _))] at ht
  simpa only [div_eq_mul_inv,mul_one,one_mul] using ht

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

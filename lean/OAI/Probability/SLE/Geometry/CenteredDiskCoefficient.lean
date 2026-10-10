import OAI.Probability.SLE.Geometry.CenteredStoppedMonotonicity
import OAI.Probability.SLE.Gauge.FiniteMomentBounds

namespace OAI

/-! The exact prescribed coefficient is a stopped canonical-mass moment
under the finite centered law, including paths with an infinite level time. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

omit [IsProbabilityMeasure P] in
lemma diskScalar_progressive (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) :
    IsProgressive (Filtration.natural B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable))
      (C.diskScalar θ hθ) := by
  intro t
  exact (compactWeightedMass_measurable _ _
    (Target.diskSourceHalfPlane_compact hθ).measurableSet).comp (C.progressive t)

omit [IsProbabilityMeasure P] in
lemma normalizedStoppedDisk_eq_finite
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ)
    (σ : Ω → WithTop ℝ≥0) (ω : Ω)
    (hs : σ ω=radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) (4*ℓ/κ))
    (hf : σ ω≠⊤) :
    massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
      (C.diskTerminalScalar θ hθ ω)
      (Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ) =
        finiteStoppedScalar (C.diskScalar θ hθ) σ ω := by
  have he := Target.levelTime_eq_radiusLevelTime κ hκ _ _ ((hc ω).const_mul _)
    (γ ω) (G ω) (F ω) (hw ω) (Target.normalizedDriver_matches κ hκ B hc h0 ω) θ ℓ hℓ
  rw [← hs] at he
  rw [he, massAtExtendedTime, ite_eq_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf),
    finiteStoppedScalar, ite_eq_right hf, normalizedDiskScalar]
  congr 1
  lift σ ω to ℝ≥0 using hf with s hs'
  simp only [ENNReal.ofReal, WithTop.untopD_coe]
  exact mul_div_cancel_left₀ s (Real.toNNReal_pos.mpr hκ).ne'

lemma levelCoefficient_eq_centered_moment
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ)
    (σ : Ω → WithTop ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) σ)
    (heσ : ∀ᵐ ω ∂P, σ ω=radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) (4*ℓ/κ)) :
    ENNReal.ofReal (Target.levelCoefficient κ W ℓ m θ) =
      ∫⁻ ω, ENNReal.ofReal (finiteStoppedScalar (C.diskScalar θ hθ) σ ω)^m
        ∂finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) (4*ℓ/κ) := by
  let w := fun ω => Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ
  let T := fun ω => Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ
  let Y := fun ω => massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
    (C.diskTerminalScalar θ hθ ω) (T ω)
  have hwM : Measurable w := (Target.measurable_fixedLevelDensity κ θ ℓ).comp
    (Target.normalizedDriver_measurable κ B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0)
  have hY : Measurable Y := C.normalizedStoppedDisk_measurable θ hθ T
    (normalized_levelTime_measurable (hBm:=hBm) hκ hc h0 F hw θ ℓ hℓ)
  have hw0 (ω) : 0≤w ω := Target.levelDensity_nonneg_of_witness κ hκ _ _ ((hc ω).const_mul _)
    (γ ω) (G ω) (F ω) (hw ω) (Target.normalizedDriver_matches κ hκ B hc h0 ω) θ hθ ℓ hℓ
  have hY0 (ω) : 0≤Y ω := C.normalizedStoppedDisk_nonneg θ hθ (T ω) ω
  have hi : Integrable (fun ω => w ω*(Y ω)^m) P := by
    apply (C.density_disk_terminal_integrable hB hc h0 hκ hκ8 F hw hgrowth m θ hθ ℓ hℓ).mono'
      (hwM.mul (hY.pow_const m)).aestronglyMeasurable
    filter_upwards [C.normalizedStoppedDisk_le_terminal hκ θ hθ T] with ω hω
    change ‖w ω*(Y ω)^m‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (hw0 ω) (pow_nonneg (hY0 ω) m))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hY0 ω) hω m) (hw0 ω)
  have hQ : finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) (4*ℓ/κ) =
      P.withDensity (fun ω => ENNReal.ofReal (w ω)) := by
    unfold finiteCenteredLaw
    congr 1
    funext ω
    dsimp only [w]
    rw [Target.levelDensity_eq_stoppedGreen κ hκ _ _ ((hc ω).const_mul _)
      (γ ω) (G ω) (F ω) (hw ω) (Target.normalizedDriver_matches κ hκ B hc h0 ω) θ hθ ℓ hℓ]
  rw [C.levelCoefficient_eq_mass hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m]
  change ENNReal.ofReal (∫ ω, w ω*(Y ω)^m ∂P)=_
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun ω => mul_nonneg (hw0 ω) (pow_nonneg (hY0 ω) m))),hQ,
    lintegral_withDensity_eq_lintegral_mul P hwM.ennreal_ofReal
      (((finiteStoppedScalar_measurable _ _ (C.diskScalar_progressive θ hθ) σ hσ).mono
        hσ.measurableSpace_le le_rfl).ennreal_ofReal.pow_const m)]
  apply lintegral_congr_ae
  filter_upwards [heσ] with ω hs
  rw [ENNReal.ofReal_mul (hw0 ω),ENNReal.ofReal_pow (hY0 ω)]
  change ENNReal.ofReal (w ω)*ENNReal.ofReal (Y ω)^m =
    ENNReal.ofReal (w ω)*ENNReal.ofReal (finiteStoppedScalar (C.diskScalar θ hθ) σ ω)^m
  by_cases hf : σ ω=⊤
  · have hT : T ω=∞ := by
      dsimp only [T]
      rw [Target.levelTime_eq_radiusLevelTime κ hκ _ _ ((hc ω).const_mul _)
        (γ ω) (G ω) (F ω) (hw ω) (Target.normalizedDriver_matches κ hκ B hc h0 ω) θ ℓ hℓ,
        ← hs,hf]
      change ENNReal.ofReal κ*(⊤:ℝ≥0∞)=∞
      exact ENNReal.mul_top (ENNReal.ofReal_pos.mpr hκ).ne'
    have hwz : w ω=0 := by
      change Target.levelDensity κ θ _ ℓ=0
      have hT' : Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ=∞ := hT
      simp only [Target.levelDensity,hT',lt_self_iff_false,ite_false]
    simp only [hwz,ENNReal.ofReal_zero,zero_mul]
  · dsimp only [Y,T]
    rw [C.normalizedStoppedDisk_eq_finite hc h0 hκ F hw θ hθ ℓ hℓ σ ω hs hf]

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

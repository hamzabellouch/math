import OAI.Probability.SLE.Gauge.FiniteMomentMonotonicity
import OAI.Probability.SLE.Loewner.ActualRadiusStopsRegular

namespace OAI

/-! Jensen inequalities for the exact stopped coefficients and their
prescribed limit. No law after the centered terminal time is used. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma centered_diskScalar_integrable_eq
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
    let Q := finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) (4*ℓ/κ)
    let X := finiteStoppedScalar (C.diskScalar θ hθ) σ
    Integrable (fun ω => X ω^m) Q ∧
      Target.levelCoefficient κ W ℓ m θ=(∫ ω, X ω^m ∂Q) := by
  dsimp only
  let Q := finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) (4*ℓ/κ)
  let X := finiteStoppedScalar (C.diskScalar θ hθ) σ
  have hX : Measurable X := (finiteStoppedScalar_measurable _ _ (C.diskScalar_progressive θ hθ) σ hσ).mono
    hσ.measurableSpace_le le_rfl
  have hX0 (ω) : 0≤X ω := by
    dsimp only [X,finiteStoppedScalar]
    split_ifs
    · exact le_rfl
    · exact compactWeightedMass_nonneg _ _ _
  have he := C.levelCoefficient_eq_centered_moment hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m σ hσ heσ
  have hp (ω) : ENNReal.ofReal (X ω^m)=ENNReal.ofReal (X ω)^m := ENNReal.ofReal_pow (hX0 ω) m
  have hi : Integrable (fun ω => X ω^m) Q := by
    apply (lintegral_ofReal_ne_top_iff_integrable (hX.pow_const m).aestronglyMeasurable
      (Eventually.of_forall (fun ω => pow_nonneg (hX0 ω) m))).mp
    simp_rw [hp]
    rw [← he]
    exact ENNReal.ofReal_ne_top
  refine ⟨hi,?_⟩
  have he' : ENNReal.ofReal (Target.levelCoefficient κ W ℓ m θ)=
      ENNReal.ofReal (∫ ω, X ω^m ∂Q) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun ω => pow_nonneg (hX0 ω) m))]
    simpa only [hp] using he
  have hc0 := (C.levelCoefficient_nonneg_integrable hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m).1 θ hθ
  have hi0 : 0≤∫ ω, X ω^m ∂Q := integral_nonneg (fun ω => pow_nonneg (hX0 ω) m)
  simpa only [ENNReal.toReal_ofReal hc0,ENNReal.toReal_ofReal hi0] using congrArg ENNReal.toReal he'

include C in
lemma levelCoefficient_jensen
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    (Target.levelCoefficient κ W ℓ 1 θ)^m≤Target.levelCoefficient κ W ℓ m θ := by
  let σ := fun ω => (radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) (4*ℓ/κ) : WithTop ℝ≥0)
  have hz := Target.diskMapInv_maps hθ (show (0:ℂ)∈Metric.ball 0 1 by simp)
  have hu : 0≤4*ℓ/κ := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  have hs := actual_radiusLevelTime_stopping hB
    (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)))
    hBm hc h0 κ hκ hκ8 γ G F hw (Target.diskMapInv θ 0) hz (4*ℓ/κ) hu
  have heσ : ∀ᵐ ω ∂P, σ ω=radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) (4*ℓ/κ) := Eventually.of_forall (fun _ => rfl)
  let Q := finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) (4*ℓ/κ)
  let : IsProbabilityMeasure Q := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F
    (Eventually.of_forall hw) _ hz _ hu
  obtain ⟨hi1,he1⟩ := C.centered_diskScalar_integrable_eq hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ 1 σ hs heσ
  obtain ⟨him,hem⟩ := C.centered_diskScalar_integrable_eq hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m σ hs heσ
  rw [he1,hem]
  simp only [pow_one] at hi1 ⊢
  refine (convexOn_pow (𝕜:=ℝ) m).map_integral_le (μ:=Q)
    (continuous_pow m).continuousOn isClosed_Ici ?_ hi1 him
  filter_upwards [] with ω
  change 0 ≤ finiteStoppedScalar (C.diskScalar θ hθ) σ ω
  dsimp only [finiteStoppedScalar]
  split_ifs
  · exact le_rfl
  · exact compactWeightedMass_nonneg _ _ _

include C in
theorem finiteMoment_jensen
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    (Target.finiteMoment κ W 1 ℓ)^m≤Target.finiteMoment κ W m ℓ := by
  let : IsProbabilityMeasure (Target.angleLaw κ) := Target.angleLaw_isProbability hκ
  obtain ⟨hn1,hi1⟩ := C.levelCoefficient_nonneg_integrable hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ 1
  obtain ⟨hnm,him⟩ := C.levelCoefficient_nonneg_integrable hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m
  have hj : ∀ᵐ θ ∂Target.angleLaw κ,
      (Target.levelCoefficient κ W ℓ 1 θ)^m≤Target.levelCoefficient κ W ℓ m θ := by
    filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
    exact C.levelCoefficient_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m
  have hp : Integrable (fun θ => (Target.levelCoefficient κ W ℓ 1 θ)^m) (Target.angleLaw κ) := by
    apply him.mono' (hi1.aestronglyMeasurable.pow m)
    filter_upwards [hj,Target.angleLaw_ae_mem κ] with θ hθ hθI
    change ‖(Target.levelCoefficient κ W ℓ 1 θ)^m‖ ≤ _
    rw [Real.norm_of_nonneg (pow_nonneg (hn1 θ hθI) m)]
    exact hθ
  rw [C.finiteMoment_eq_levelCoefficientIntegral hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ 1,
    C.finiteMoment_eq_levelCoefficientIntegral hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m]
  apply le_trans ((convexOn_pow (𝕜:=ℝ) m).map_integral_le (continuous_pow m).continuousOn isClosed_Ici
    (by filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ; exact hn1 θ hθ) hi1 hp)
  exact integral_mono_ae hp him hj

include C in
theorem moment_jensen
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (m : ℕ) : (Target.moment κ W 1)^m≤Target.moment κ W m := by
  exact le_of_tendsto_of_tendsto
    ((C.finiteMoment_tendsto_moment hB hc h0 hκ hκ8 F hw hgrowth W hW 1).pow m)
    (C.finiteMoment_tendsto_moment hB hc h0 hκ hκ8 F hw hgrowth W hW m)
    (Eventually.of_forall (fun ℓ => C.finiteMoment_jensen hB hc h0 hκ hκ8 F hw hgrowth W hW
      ℓ (Nat.cast_nonneg ℓ) m))

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

import OAI.Probability.SLE.Geometry.CanonicalJointDisk
import OAI.Probability.SLE.Gauge.ExactMomentGauge

namespace OAI

/-! The actual finite centered law with the prescribed initial angle mixture.
Its moments are exactly the finite coefficients in the gauge construction. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def centeredDiskDensity {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (u : ℝ) (p : ℝ × Ω) : ℝ≥0∞ :=
  canonicalFiniteDensity κ (u,Target.diskMapInv p.1 0,sourceDriverPath B hc p.2)

def centeredDiskLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω)) (u : ℝ) :
    Measure (ℝ × Ω) :=
  ((Target.angleLaw κ).prod P).withDensity (centeredDiskDensity κ B hc u)

lemma centeredDiskDensity_measurable {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω)) (u : ℝ) :
    Measurable (centeredDiskDensity κ B hc u) := by
  apply (canonicalFiniteDensity_measurable κ).comp
  apply measurable_const.prodMk
  apply Measurable.prodMk
  · unfold Target.diskMapInv
    fun_prop
  · exact (source_path_measurable (sourceDriverPath B hc) hm).comp measurable_snd

lemma centeredDiskLaw_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (κ : ℝ) (hκ : 0 < κ)
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0 ≤ u) (f : ℝ × Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂centeredDiskLaw P κ B hc u) =
      ∫⁻ θ, ∫⁻ ω, f (θ,ω) ∂finiteCenteredLaw P κ B γ G (Target.diskMapInv θ 0) u
        ∂Target.angleLaw κ := by
  let : IsProbabilityMeasure (Target.angleLaw κ) := Target.angleLaw_isProbability hκ
  have hd := centeredDiskDensity_measurable κ B hm hc u
  rw [centeredDiskLaw,lintegral_withDensity_eq_lintegral_mul _ hd hf,
    lintegral_prod _ (hd.mul hf).aemeasurable]
  apply lintegral_congr
  intro θ
  have hdθ : Measurable (fun ω => ENNReal.ofReal
      (stoppedGreen κ (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω)
        (Target.diskMapInv θ 0) u / initialGreen κ (Target.diskMapInv θ 0))) := by
    have hmθ : Measurable (fun ω : Ω => (θ,ω)) := measurable_const.prodMk measurable_id
    have h : Measurable (fun ω : Ω => centeredDiskDensity κ B hc u (θ,ω)) := hd.comp hmθ
    convert h using 1
    funext ω
    exact (canonicalFiniteDensity_eq κ (sourceDriverPath B hc ω) (hw ω) u hu _).symm
  have hfθ : Measurable (fun ω : Ω => f (θ,ω)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [finiteCenteredLaw,lintegral_withDensity_eq_lintegral_mul _ hdθ hfθ]
  apply lintegral_congr
  intro ω
  change centeredDiskDensity κ B hc u (θ,ω) * f (θ,ω) = _
  dsimp only [centeredDiskDensity]
  rw [canonicalFiniteDensity_eq κ (sourceDriverPath B hc ω) (hw ω) u hu]
  rfl

lemma centeredDiskLaw_isProbability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0<κ) (hκ8 : κ<8) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (hu : 0≤u) : IsProbabilityMeasure (centeredDiskLaw P κ B hc u) := by
  let : IsProbabilityMeasure (Target.angleLaw κ) := Target.angleLaw_isProbability hκ
  constructor
  rw [← lintegral_one,centeredDiskLaw_lintegral P κ hκ B
    (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hc γ G F hw u hu
    (fun _ => 1) measurable_const]
  calc
    _ = ∫⁻ _θ, (1 : ℝ≥0∞) ∂Target.angleLaw κ := by
      apply lintegral_congr_ae
      filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
      let := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F (Eventually.of_forall hw)
        (Target.diskMapInv θ 0) (Target.diskMapInv_maps hθ (by simp)) u hu
      simp
    _ = 1 := by simp

namespace Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma centeredDiskLaw_moment
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    (∫⁻ p, ENNReal.ofReal (C.diskAtRadius p.1 (4*ℓ/κ) p.2)^m
      ∂centeredDiskLaw P κ B hc (4*ℓ/κ)) = ENNReal.ofReal (Target.finiteMoment κ W m ℓ) := by
  have hu : 0 ≤ 4*ℓ/κ := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  rw [centeredDiskLaw_lintegral P κ hκ B
    (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hc γ G F hw _ hu _
    ((C.diskAtRadius_joint_measurable hc F hw _ hu).ennreal_ofReal.pow_const m)]
  calc
    _ = ∫⁻ θ, ENNReal.ofReal (Target.levelCoefficient κ W ℓ m θ) ∂Target.angleLaw κ := by
      apply lintegral_congr_ae
      filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
      exact (C.levelCoefficient_eq_diskAtRadius_moment hB hc h0 hκ hκ8 F hw hgrowth W hW
        θ hθ ℓ hℓ m).symm
    _ = _ := by
      rw [C.finiteMoment_eq_levelCoefficientIntegral hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m]
      symm
      apply ofReal_integral_eq_lintegral_ofReal
        (C.levelCoefficient_nonneg_integrable hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m).2
      filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
      exact (C.levelCoefficient_nonneg_integrable hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m).1 θ hθ

end Multipoint.CanonicalMass
end SLEExactGauge

end

end OAI

import OAI.Probability.SLE.Angle.RadiusAngleKernel

namespace OAI

/-! Bounds on the canonical angle transition transfer to every event in
the actual radius-stopped past. No angular mixing bound is assumed globally. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
local instance angleBoundsMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance angleBoundsBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma finiteCenteredLaw_extended_angle_mem
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z∈upperHalfPlane) (u V : ℝ) (hu : 0≤u) (huV : u≤V) :
    ∀ᵐ ω ∂finiteCenteredLaw P κ B γ G z V,
      extendedMarkedAngle κ B γ G (fun ω => radiusLevelTime (γ ω) (G ω) z u) z ω∈
        Ioo (0:ℝ) Real.pi := by
  let σ : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  have hfinite : ∀ᵐ ω ∂finiteCenteredLaw P κ B γ G z V, σ ω≠⊤ :=
    finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F (Eventually.of_forall hw)
      z hz u V hu huV σ (Eventually.of_forall fun _ => le_rfl)
  filter_upwards [hfinite] with ω hω
  have hstate := actual_radius_level_finite_state (hw ω) ((hc ω).const_mul _) z u hω
  have hp := (hw ω).live_marked_polar ((σ ω).untopD 0) z hstate.1
  change extendedMarkedAngle κ B γ G σ z ω∈Ioo (0:ℝ) Real.pi
  dsimp only [extendedMarkedAngle]
  rw [ite_eq_right hω,stoppedMarkedCenter_eq κ B γ G _ z ω hstate.1]
  exact hp.2.1

theorem radius_angle_average_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (z : ℂ) (hz : z∈upperHalfPlane) (u v V : ℝ) (hu : 0≤u) (hv : 0<v) (hV : u+v≤V)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) (c C : ℝ≥0∞)
    (hbound : ∀ θ∈Ioo (0:ℝ) Real.pi,
      c≤canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f θ ∧
      canonicalAngleAverage (P.map (sourceDriverPath B hc)) κ v f θ≤C)
    (A : Set Ω) (hA : MeasurableSet[(actual_radiusLevelTime_stopping hB
      (fun t => (hBm.of_uncurry_left : Measurable (B t))) hBm hc h0
      κ hκ hκ8 γ G F hw z hz u hu).measurableSpace] A) :
    c*finiteCenteredLaw P κ B γ G z V A ≤
      (∫⁻ ω in A, f (extendedMarkedAngle κ B γ G
        (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)) z ω)
        ∂finiteCenteredLaw P κ B γ G z V) ∧
    (∫⁻ ω in A, f (extendedMarkedAngle κ B γ G
        (fun ω => radiusLevelTime (γ ω) (G ω) z (u+v)) z ω)
        ∂finiteCenteredLaw P κ B γ G z V) ≤ C*finiteCenteredLaw P κ B γ G z V A := by
  rw [← radius_angle_kernel hB hBm hc h0 hκ hκ8 γ G F hw hpublished z hz u v V hu hv hV f hf A hA]
  have hang := finiteCenteredLaw_extended_angle_mem hB hc hκ hκ8 γ G F hw z hz u V hu
    (by linarith)
  constructor
  · calc
      _ = ∫⁻ _ω in A, c ∂finiteCenteredLaw P κ B γ G z V := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hang] with ω hω
        exact (hbound _ hω).1
  · calc
      _ ≤ ∫⁻ _ω in A, C ∂finiteCenteredLaw P κ B γ G z V := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hang] with ω hω
        exact (hbound _ hω).2
      _ = _ := by simp

end SLEExactGauge

end

end OAI

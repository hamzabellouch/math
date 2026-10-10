import OAI.Probability.SLE.Geometry.CanonicalRestartWitness
import OAI.Probability.SLE.Loewner.RestartDriverScaling
import OAI.Probability.SLE.Geometry.NormalizedRestartKernel
import OAI.Probability.SLE.Geometry.BoundaryScaleLaw

namespace OAI

/-! Canonical capacity witnesses and finite boundary charts for the actual
restart normalized by a positive scale measurable in the stopped past. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open BoundaryScaleLaw

local instance normalizedCanonicalDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance normalizedCanonicalDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance normalizedCanonicalPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance normalizedCanonicalPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
local instance : LocallyCompactSpace closedHalfPlane :=
  isClosed_closedHalfPlane.locallyCompactSpace

def normalizedRestartDriverPath
    {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ a : Ω → ℝ≥0) (ω : Ω) : C(ℝ≥0, ℝ) :=
  scaleDriverPath ((a ω)⁻¹) (sourceRestartDriverPath B hc τ ω)

lemma normalizedRestartDriverPath_driver
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ a : Ω → ℝ≥0) (ω : Ω) :
    (fun t => Real.sqrt κ * normalizedRestartDriverPath B hc τ a ω t) =
      normalizedRestartDriver (fun t => Real.sqrt κ * B t ω) (τ ω) (a ω) := by
  funext t
  have htime : sourceScaleTime ((a ω)⁻¹) t = (a ω) ^ 2 * t := by
    simp only [sourceScaleTime, div_eq_mul_inv, inv_pow, inv_inv, mul_comm]
  change Real.sqrt κ * (((a ω)⁻¹ : ℝ≥0) *
      (B (τ ω + sourceScaleTime ((a ω)⁻¹) t) ω - B (τ ω) ω)) = _
  rw [htime]
  simp only [normalizedRestartDriver, NNReal.coe_inv, div_eq_mul_inv]
  ring

lemma measurable_boundary_scale_family
    {X : Type*} [MeasurableSpace X]
    (Fb : X → C(closedHalfPlane, ℂ)) (hFb : Measurable Fb)
    (a : X → ℝ≥0) (ha : Measurable a) :
    Measurable (fun x => (Fb x).comp (scaleClosed (a x))) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro z
  have hz : Measurable (fun x => scaleClosed (a x) z) := by
    apply Measurable.subtype_mk
    exact (Complex.measurable_ofReal.comp (NNReal.continuous_coe.measurable.comp ha)).mul_const
      (z : ℂ)
  exact continuous_eval.measurable.comp (hFb.prodMk hz)

/-- The same canonical trace factor realizes every positive, past-measurable
normalization of the restart, with its actual capacity witness and an
all-time identity through the corresponding finite boundary chart. -/
theorem source_normalized_canonical_witness_boundary_restart
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (a : Ω → ℝ≥0) (ham : Measurable[hτ.measurableSpace] a) (ha : ∀ ω, 0 < a ω) :
    ∃ (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
      (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ) (Fb : Ω → C(closedHalfPlane, ℂ)),
      Measurable Φ ∧ Measurable[hτ.measurableSpace] Fb ∧
      Measurable (normalizedRestartDriverPath B hc τ a) ∧
      (∀ᵐ ω ∂P, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
      (∀ᵐ p ∂P.map (sourceDriverPath B hc),
        IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p)) ∧
      (∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane →
        Fb ω z = F ω (τ ω) ((a ω : ℂ) * z + (Real.sqrt κ * B (τ ω) ω : ℝ))) ∧
      (∀ ω, Fb ω ⟨0, by simp [closedHalfPlane]⟩ = γ ω (τ ω)) ∧
      (∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
        (P.restrict A).map (normalizedRestartDriverPath B hc τ a) =
          P A • P.map (sourceDriverPath B hc)) ∧
      ∀ᵐ ω ∂P,
        IsCapacityTwoWitness
          (normalizedRestartDriver (fun t => Real.sqrt κ * B t ω) (τ ω) (a ω))
          (Φ (normalizedRestartDriverPath B hc τ a ω))
          (Gc (normalizedRestartDriverPath B hc τ a ω))
          (Fc (normalizedRestartDriverPath B hc τ a ω)) ∧
        ∀ t : ℝ≥0, γ ω (τ ω + (a ω) ^ 2 * t) =
          finiteBoundaryPath (Fb ω) (Φ (normalizedRestartDriverPath B hc τ a ω)) t := by
  obtain ⟨Φ, Gc, Fc, Fb₀, hΦ, hFb₀, hW, hFb₀eq, hFb₀zero, _htraceLaw, hrestart⟩ :=
    source_canonical_witness_boundary_restart κ hκ hκ8 B hB hm hc γ G F hw
      hpublished hboundary τ hτ
  let bp := sourceDriverPath B hc
  let rp := sourceRestartDriverPath B hc τ
  let Y := normalizedRestartDriverPath B hc τ a
  let Fb : Ω → C(closedHalfPlane, ℂ) := fun ω => (Fb₀ ω).comp (scaleClosed (a ω))
  have hbp : Measurable bp := source_path_measurable bp hm
  have hrp : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have haAmbient : Measurable a := ham.mono hτ.measurableSpace_le le_rfl
  have hY : Measurable Y :=
    measurable_scaleDriverPath.comp (haAmbient.inv.prodMk hrp)
  have hYlaw (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
      (P.restrict A).map Y = P A • P.map bp :=
    source_restart_random_scale_driver_law B hB hm hc τ hτ (fun ω => (a ω)⁻¹)
      ham.inv (fun ω => inv_pos.mpr (ha ω)) A hA
  have hYlaw₀ : P.map Y = P.map bp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using hYlaw univ MeasurableSet.univ
  have hYw := canonical_witness_pullback hW Y hY hYlaw₀
  have hbpw := canonical_witness_pullback hW bp hbp rfl
  have hΦorig : ∀ᵐ ω ∂P, Φ (bp ω) = sourceTracePath γ (fun ω => (hw ω).1) ω := by
    filter_upwards [hbpw] with ω hω
    ext t
    exact congrFun (hω.trace_unique (hw ω)) t
  have hFb : Measurable[hτ.measurableSpace] Fb :=
    @measurable_boundary_scale_family Ω hτ.measurableSpace Fb₀ hFb₀ a ham
  refine ⟨Φ, Gc, Fc, Fb, hΦ, hFb, hY, hΦorig, hW, ?_, ?_, hYlaw, ?_⟩
  · intro ω z hz
    have hscaled : (scaleClosed (a ω) z : ℂ) ∈ upperHalfPlane := by
      change 0 < ((a ω : ℂ) * z).im
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        using mul_pos (show 0 < (a ω : ℝ) from ha ω) hz
    exact hFb₀eq ω (scaleClosed (a ω) z) hscaled
  · intro ω
    change Fb₀ ω ⟨(a ω : ℂ) * 0, _⟩ = γ ω (τ ω)
    simpa only [mul_zero] using hFb₀zero ω
  · filter_upwards [hYw, hrestart] with ω hω hωrestart
    have hactual : IsCapacityTwoWitness
        (normalizedRestartDriver (fun t => Real.sqrt κ * B t ω) (τ ω) (a ω))
        (Φ (Y ω)) (Gc (Y ω)) (Fc (Y ω)) := by
      rw [← normalizedRestartDriverPath_driver κ B hc τ a ω]
      exact hω
    have hup : IsCapacityTwoWitness (fun t => Real.sqrt κ * rp ω t)
        (sourceScaleTrace (a ω) (Φ (Y ω)))
        (sourceScaleChart (a ω) (Gc (Y ω)))
        (sourceScaleChart (a ω) (Fc (Y ω))) := by
      convert normalized_restart_witness (τ ω) (a ω) (ha ω) hactual using 1
      funext t
      change Real.sqrt κ * (B (τ ω + t) ω - B (τ ω) ω) =
        Real.sqrt κ * B (τ ω + t) ω - Real.sqrt κ * B (τ ω) ω
      ring
    have heq : Φ (rp ω) = ScaleTraceLaw.scalePath (a ω) (Φ (Y ω)) := by
      ext t
      exact (congrFun (hup.trace_unique hωrestart.1) t).symm
    refine ⟨hactual, ?_⟩
    intro t
    have hclosed : ClosedPathProperty (Φ (Y ω)) := fun t => hω.2.2.1 t
    have hclock := congrArg (fun p : C(ℝ≥0, ℂ) => p t)
      (boundary_scale_clock_identity (a ω) (ha ω) (Fb₀ ω) (Φ (Y ω)) hclosed)
    change finiteBoundaryPath (Fb ω) (Φ (Y ω)) t =
      finiteBoundaryPath (Fb₀ ω) (ScaleTraceLaw.scalePath (a ω) (Φ (Y ω))) ((a ω) ^ 2 * t)
      at hclock
    rw [← heq] at hclock
    exact (hωrestart.2 ((a ω) ^ 2 * t)).trans hclock.symm

end SLEExactGauge

end

end OAI

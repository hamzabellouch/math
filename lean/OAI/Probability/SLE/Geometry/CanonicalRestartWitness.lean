import OAI.Probability.SLE.Geometry.PublishedInputs
import OAI.Probability.SLE.Loewner.TraceWitnessUniqueness
import OAI.Probability.SLE.Geometry.FiniteBoundaryRestart

namespace OAI

/-! Actual capacity witnesses for the fresh driver path. The trace-generation
input is Rohde--Schramm's existing input on the single canonical driver law.
Deterministic uniqueness identifies the resulting measurable trace factor
with the factor in the proved stopped trace law. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance canonicalDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance canonicalDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance canonicalTraceMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance canonicalTraceBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

/-- Evaluation on the canonical continuous-driver law is the same Brownian
motion law, so the trace-generation input below is applied to a Brownian driver. -/
theorem canonical_driver_isBrownian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω)) :
    IsBrownianReal (fun (t : ℝ≥0) (p : C(ℝ≥0, ℝ)) => p t)
      (P.map (sourceDriverPath B hc)) := by
  have hbp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  refine ⟨⟨fun I => ?_⟩, Eventually.of_forall (fun p => p.continuous)⟩
  have hI : Measurable (fun p : C(ℝ≥0, ℝ) => I.restrict (fun t => p t)) :=
    Measurable.of_eval (fun i => (continuous_eval_const (i : ℝ≥0)).measurable)
  refine ⟨hI.aemeasurable, ?_⟩
  rw [Measure.map_map hI hbp]
  exact (hB.hasLaw I).map_eq

theorem exists_measurable_canonical_witness
    (ν : Measure C(ℝ≥0, ℝ)) (κ : ℝ)
    (hpublished : PublishedTraceGeneration ν κ (fun t p => p t)) :
    ∃ (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
      (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ), Measurable Φ ∧
      ∀ᵐ p ∂ν, IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p) := by
  classical
  obtain ⟨γ, hm, htrace⟩ := hpublished
  obtain ⟨S, hSa, hSm, hS⟩ := htrace.exists_measurable_mem
  choose G F hw using fun p : S => hS p p.property
  let g : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ := fun p t => if p ∈ S then γ p t else 0
  have hg (p : C(ℝ≥0, ℝ)) : Continuous (g p) := by
    by_cases hp : p ∈ S
    · simpa only [g, ite_eq_left hp] using (hw ⟨p, hp⟩).1
    · simpa only [g, ite_eq_right hp] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℂ)))
  let Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ) := fun p => ⟨g p, hg p⟩
  let Gc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ := fun p =>
    if hp : p ∈ S then G ⟨p, hp⟩ else fun _ _ => 0
  let Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ := fun p =>
    if hp : p ∈ S then F ⟨p, hp⟩ else fun _ _ => 0
  refine ⟨Φ, Gc, Fc, ?_, ?_⟩
  · apply source_path_measurable
    intro t
    change Measurable (fun p => if p ∈ S then γ p t else 0)
    exact Measurable.ite hSm (hm t) measurable_const
  · filter_upwards [hSa] with p hp
    change IsCapacityTwoWitness _ (g p) (Gc p) (Fc p)
    simpa only [g, Gc, Fc, ite_eq_left hp, dite_eq_left hp] using hw ⟨p, hp⟩

theorem canonical_witness_pullback
    {ν : Measure C(ℝ≥0, ℝ)} {κ : ℝ}
    {Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ)}
    {Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ}
    (hw : ∀ᵐ p ∂ν, IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Y : Ω → C(ℝ≥0, ℝ)) (hY : Measurable Y) (hlaw : P.map Y = ν) :
    ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun t => Real.sqrt κ * Y ω t)
      (Φ (Y ω)) (Gc (Y ω)) (Fc (Y ω)) := by
  apply ae_of_ae_map (p := fun p : C(ℝ≥0, ℝ) =>
    IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p)) hY.aemeasurable
  rwa [hlaw]

theorem canonical_witness_original_trace
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t)) :
    ∃ (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
      (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ), Measurable Φ ∧
      (∀ᵐ p ∂P.map (sourceDriverPath B hc),
        IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p)) ∧
      ∀ᵐ ω ∂P, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω := by
  obtain ⟨Φ, Gc, Fc, hΦm, hΦw⟩ := exists_measurable_canonical_witness _ κ hpublished
  refine ⟨Φ, Gc, Fc, hΦm, hΦw, ?_⟩
  have hbp := source_path_measurable (sourceDriverPath B hc) hm
  filter_upwards [ae_of_ae_map hbp.aemeasurable hΦw] with ω hω
  have hω' : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (Φ (sourceDriverPath B hc ω)) (Gc (sourceDriverPath B hc ω)) (Fc (sourceDriverPath B hc ω)) := hω
  have he := hω'.trace_unique (hw ω)
  ext t
  exact congrFun he t

/-- The same fresh path has an actual capacity witness and realizes the
all-time finite-boundary restart identity. The only new instance of trace
generation is its explicit specialization to the original driver path law. -/
theorem source_canonical_witness_boundary_restart
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
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ (Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ))
      (Gc Fc : C(ℝ≥0, ℝ) → ℝ≥0 → ℂ → ℂ) (Fb : Ω → C(closedHalfPlane, ℂ)),
      Measurable Φ ∧ Measurable[hτ.measurableSpace] Fb ∧
      (∀ᵐ p ∂P.map (sourceDriverPath B hc),
        IsCapacityTwoWitness (fun t => Real.sqrt κ * p t) (Φ p) (Gc p) (Fc p)) ∧
      (∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane →
        Fb ω z = F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ))) ∧
      (∀ ω, Fb ω ⟨0, by simp [closedHalfPlane]⟩ = γ ω (τ ω)) ∧
      (∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
        (P.restrict A).map (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) =
          P A • P.map (sourceTracePath γ (fun ω => (hw ω).1))) ∧
      ∀ᵐ ω ∂P,
        IsCapacityTwoWitness (fun t => Real.sqrt κ * sourceRestartDriverPath B hc τ ω t)
          (Φ (sourceRestartDriverPath B hc τ ω))
          (Gc (sourceRestartDriverPath B hc τ ω)) (Fc (sourceRestartDriverPath B hc τ ω)) ∧
        ∀ t : ℝ≥0, γ ω (τ ω + t) =
          finiteBoundaryPath (Fb ω) (Φ (sourceRestartDriverPath B hc τ ω)) t := by
  obtain ⟨Φ, Gc, Fc, hΦm, hΦw, hΦorig⟩ :=
    canonical_witness_original_trace P κ B hm hc γ G F hw hpublished
  obtain ⟨Ψ, Fb, hΨm, hΨorig, hFbm, hFb, hFb0, hΨlaw, hΨrestart⟩ :=
    source_measurable_finite_boundary_restart κ hκ hκ8 B hB hm hc γ G F hw hboundary τ hτ
  let bp := sourceDriverPath B hc
  let rp := sourceRestartDriverPath B hc τ
  have hbp : Measurable bp := source_path_measurable bp hm
  have hrp : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have heq : ∀ᵐ p ∂P.map bp, Φ p = Ψ p := by
    apply (ae_map_iff hbp.aemeasurable (measurableSet_eq_fun hΦm hΨm)).mpr
    filter_upwards [hΦorig] with ω hω
    exact hω.trans (hΨorig ω).symm
  have hlaw : P.map rp = P.map bp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using
      source_restart_continuous_driver_law hB hm hc τ hτ (A := univ) MeasurableSet.univ
  have hrEq : ∀ᵐ ω ∂P, Φ (rp ω) = Ψ (rp ω) := by
    apply ae_of_ae_map (p := fun p : C(ℝ≥0, ℝ) => Φ p = Ψ p) hrp.aemeasurable
    rwa [hlaw]
  refine ⟨Φ, Gc, Fc, Fb, hΦm, hFbm, hΦw, hFb, hFb0, ?_, ?_⟩
  · intro A hA
    calc
      _ = (P.restrict A).map (fun ω => Ψ (rp ω)) :=
        Measure.map_congr (hrEq.filter_mono (ae_mono Measure.restrict_le_self))
      _ = _ := hΨlaw A hA
  · have hrw := canonical_witness_pullback hΦw rp hrp hlaw
    filter_upwards [hrw, hrEq, hΨrestart] with ω hω heω hrestart
    refine ⟨hω, ?_⟩
    intro t
    rw [heω]
    exact hrestart t

end SLEExactGauge

end

end OAI

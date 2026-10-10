import OAI.Probability.SLE.Geometry.PublishedFiniteBoundaryExtension
import OAI.Probability.SLE.Geometry.MeasurableBoundaryRestart

namespace OAI

/-! Finite-valued boundary charts introduce no measurable selection into
an actual stopped restart: their boundary evaluations are determined by the
interior map. The same past-measurable family realizes all future times. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance : LocallyCompactSpace closedHalfPlane :=
  isClosed_closedHalfPlane.locallyCompactSpace
local instance finiteRestartPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance finiteRestartPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
local instance finiteRestartDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance finiteRestartDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma closed_halfplane_map_ext {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f g : C(closedHalfPlane, Y))
    (heq : ∀ z : closedHalfPlane, z.1 ∈ upperHalfPlane → f z = g z) : f = g := by
  ext z
  let zₙ (n : ℕ) : closedHalfPlane :=
    ⟨z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I, by
      change 0 ≤ (z.1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      exact add_nonneg z.2 (by positivity)⟩
  have hH (n : ℕ) : (zₙ n).1 ∈ upperHalfPlane := by
    change 0 < (z.1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    exact add_pos_of_nonneg_of_pos z.2 (by positivity)
  have hz : Tendsto zₙ atTop (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul, add_zero] using
      tendsto_const_nhds.add (((Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const Complex.I)
  exact tendsto_nhds_unique ((f.continuous.tendsto z).comp hz)
    (((g.continuous.tendsto z).comp hz).congr (fun n => (heq (zₙ n) (hH n)).symm))

lemma finite_boundary_extension_family_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℂ → ℂ) (Fb : Ω → C(closedHalfPlane, ℂ))
    (hf : ∀ z ∈ upperHalfPlane, Measurable (fun ω => f ω z))
    (hext : ∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane → Fb ω z = f ω z) :
    Measurable Fb := by
  let Fc : Ω → C(closedHalfPlane, OnePoint ℂ) := fun ω =>
    ⟨fun z => (Fb ω z : OnePoint ℂ), OnePoint.continuous_coe.comp (Fb ω).continuous⟩
  apply ContinuousMap.measurable_iff_eval.mpr
  intro z
  have hc := boundary_extension_eval_measurable f Fc hf
    (fun ω w hw => congrArg (fun v : ℂ => (v : OnePoint ℂ)) (hext ω w hw)) z
  exact OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurable_comp_iff.mp hc

/-- Finite boundary evaluations are determined by the stopping-time past. -/
theorem source_stopped_finiteBoundaryPath_measurable
    (hpublished : PublishedFiniteLoewnerBoundaryExtension)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ Fb : Ω → C(closedHalfPlane, ℂ),
      Measurable[hτ.measurableSpace] Fb ∧
      (∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane →
        Fb ω z = F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ))) ∧
      ∀ ω, Fb ω ⟨0, by simp [closedHalfPlane]⟩ = γ ω (τ ω) := by
  choose Fb hext htip using fun ω =>
    normalized_finite_capacity_inverse_boundary_extension hpublished
      (continuous_const.mul (hc ω)) (hw ω) (τ ω) 1 zero_lt_one
  have he (ω : Ω) (z : closedHalfPlane) (hz : z.1 ∈ upperHalfPlane) :
      Fb ω z = F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ)) := by
    simpa only [Complex.ofReal_one, one_mul, add_comm, Pi.mul_apply] using hext ω z hz
  refine ⟨Fb, ?_, he, htip⟩
  apply @finite_boundary_extension_family_measurable Ω hτ.measurableSpace
    (fun ω z => F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ))) Fb _ he
  intro z hz
  exact (continuous_eval_const (⟨z, hz⟩ : upperHalfPlane)).measurable.comp
    (source_stopped_inversePath_measurable B hm hc κ γ G F hw τ hτ)

/-- The actual future trace is the finite boundary image of the fresh
trace, using a chart measurable in precisely the same stopped past. -/
theorem source_measurable_finite_boundary_restart
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (hpublished : PublishedFiniteLoewnerBoundaryExtension)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), ∃ Fb : Ω → C(closedHalfPlane, ℂ),
      Measurable Φ ∧
      (∀ ω, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
      Measurable[hτ.measurableSpace] Fb ∧
      (∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane →
        Fb ω z = F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ))) ∧
      (∀ ω, Fb ω ⟨0, by simp [closedHalfPlane]⟩ = γ ω (τ ω)) ∧
      (∀ A : Set Ω, MeasurableSet[hτ.measurableSpace] A →
        (P.restrict A).map (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) =
          P A • P.map (sourceTracePath γ (fun ω => (hw ω).1))) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        γ ω (τ ω + t) =
          finiteBoundaryPath (Fb ω) (Φ (sourceRestartDriverPath B hc τ ω)) t := by
  obtain ⟨Φ, Fc, hΦm, hΦ, _, hFc, _, hlaw, hrestart⟩ :=
    source_measurable_boundary_restart κ hκ hκ8 B hB hm hc γ G F hw
      hpublished.to_onePoint τ hτ
  obtain ⟨Fb, hFbm, hFb, hFb0⟩ := source_stopped_finiteBoundaryPath_measurable
    hpublished B hm hc κ γ G F hw τ hτ
  have he (ω : Ω) :
      (⟨fun z => (Fb ω z : OnePoint ℂ),
        OnePoint.continuous_coe.comp (Fb ω).continuous⟩ :
        C(closedHalfPlane, OnePoint ℂ)) = Fc ω := by
    apply closed_halfplane_map_ext
    intro z hz
    exact (congrArg (fun w : ℂ => (w : OnePoint ℂ)) (hFb ω z hz)).trans
      (hFc ω z hz).symm
  refine ⟨Φ, Fb, hΦm, hΦ, hFbm, hFb, hFb0, hlaw, ?_⟩
  filter_upwards [hrestart] with ω hω
  intro t
  apply OnePoint.coe_injective
  rw [hω t]
  exact (congrArg (fun f : C(closedHalfPlane, OnePoint ℂ) =>
    f (liftClosedPath (Φ (sourceRestartDriverPath B hc τ ω)) t)) (he ω)).symm

end SLEExactGauge

end

end OAI

import OAI.Probability.SLE.ChartMeasurability
import OAI.Probability.SLE.Geometry.PublishedBoundaryExtension
import Mathlib.Topology.Compactification.OnePoint.Sphere

namespace OAI

/-! Boundary charts are measurable from the stopped past. Their values on
the real line are limits of measurable interior values, so choosing the
published continuous extension introduces no additional random information.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal

namespace SLEExactGauge

abbrev closedHalfPlane : Set ℂ := {z | 0 ≤ z.im}

theorem isClosed_closedHalfPlane : IsClosed closedHalfPlane :=
  isClosed_le continuous_const Complex.continuous_im

instance onePointComplexPolishSpace : PolishSpace (OnePoint ℂ) :=
  (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3)
    (by simp [Complex.finrank_real_complex])).isClosedEmbedding.polishSpace

instance onePointComplexMeasurableSpace : MeasurableSpace (OnePoint ℂ) := borel _
instance onePointComplexBorelSpace : BorelSpace (OnePoint ℂ) := ⟨rfl⟩

local instance : LocallyCompactSpace closedHalfPlane :=
  isClosed_closedHalfPlane.locallyCompactSpace
local instance : PolishSpace closedHalfPlane := isClosed_closedHalfPlane.polishSpace
local instance : Nonempty closedHalfPlane := ⟨⟨0, by simp [closedHalfPlane]⟩⟩
local instance : MeasurableSpace C(closedHalfPlane, OnePoint ℂ) := borel _
local instance : BorelSpace C(closedHalfPlane, OnePoint ℂ) := ⟨rfl⟩

/-- A boundary evaluation is the limit along vertical interior approaches. -/
theorem boundary_extension_eval_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℂ → ℂ) (Fb : Ω → C(closedHalfPlane, OnePoint ℂ))
    (hf : ∀ z ∈ upperHalfPlane, Measurable (fun ω => f ω z))
    (hext : ∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane →
      Fb ω z = (f ω z : OnePoint ℂ))
    (z : closedHalfPlane) : Measurable (fun ω => Fb ω z) := by
  let zₙ (n : ℕ) : closedHalfPlane :=
    ⟨z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I,
      by
        change 0 ≤ (z.1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
          add_zero]
        exact add_nonneg z.2 (by positivity)⟩
  have hH (n : ℕ) : (zₙ n).1 ∈ upperHalfPlane := by
    change 0 < (zₙ n).1.im
    change 0 < (z.1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    exact add_pos_of_nonneg_of_pos z.2 (by positivity)
  have hz : Tendsto zₙ atTop (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    have hlim : Tendsto (fun n : ℕ =>
        z.1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝 z.1) := by
      simpa only [Function.comp_def, Complex.ofReal_zero, zero_mul, add_zero] using
        tendsto_const_nhds.add (((Complex.continuous_ofReal.tendsto 0).comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const Complex.I)
    exact hlim
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => Fb ω (zₙ n))
  · intro n
    have he : (fun ω => Fb ω (zₙ n)) = fun ω => (f ω (zₙ n) : OnePoint ℂ) :=
      funext (fun ω => hext ω _ (hH n))
    rw [he]
    exact OnePoint.continuous_coe.measurable.comp (hf _ (hH n))
  · exact tendsto_pi_nhds.mpr (fun ω => (Fb ω).continuous.tendsto z |>.comp hz)

/-- Borel measurability of a closed-half-plane continuous map is detected
by its evaluations on a countable dense set. -/
theorem closed_halfplane_boundary_map_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (Fb : Ω → C(closedHalfPlane, OnePoint ℂ))
    (hFb : ∀ z, Measurable (fun ω => Fb ω z)) : Measurable Fb :=
  ContinuousMap.measurable_iff_eval.mpr hFb

theorem boundary_extension_family_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℂ → ℂ) (Fb : Ω → C(closedHalfPlane, OnePoint ℂ))
    (hf : ∀ z ∈ upperHalfPlane, Measurable (fun ω => f ω z))
    (hext : ∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane →
      Fb ω z = (f ω z : OnePoint ℂ)) : Measurable Fb :=
  closed_halfplane_boundary_map_measurable Fb
    (boundary_extension_eval_measurable f Fb hf hext)

/-- The actual normalized inverse at a finite stopping time admits a
past-measurable family of continuous boundary extensions. -/
theorem source_stopped_boundaryPath_measurable
    (hpublished : PublishedLoewnerBoundaryExtension)
    {Ω : Type*} [m : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ Fb : Ω → C(closedHalfPlane, OnePoint ℂ),
      Measurable[hτ.measurableSpace] Fb ∧
      (∀ ω (z : closedHalfPlane), z.1 ∈ upperHalfPlane →
        Fb ω z = (F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ)) : OnePoint ℂ)) ∧
      ∀ ω, Fb ω ⟨0, by simp [closedHalfPlane]⟩ = (γ ω (τ ω) : OnePoint ℂ) := by
  choose Fb hcont hext htip using fun ω =>
    normalized_capacity_inverse_boundary_extension hpublished
      (continuous_const.mul (hc ω)) (hw ω) (τ ω) 1 zero_lt_one
  let fbar (ω : Ω) : C(closedHalfPlane, OnePoint ℂ) :=
    ⟨fun z => Fb ω z, (hcont ω).domRestrict⟩
  have hext' (ω : Ω) (z : closedHalfPlane) (hz : z.1 ∈ upperHalfPlane) :
      fbar ω z = (F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ)) : OnePoint ℂ) := by
    change Fb ω z = _
    simpa only [Complex.ofReal_one, one_mul, add_comm,
      Pi.mul_apply]
      using hext ω z hz
  refine ⟨fbar, ?_, hext', fun ω => htip ω⟩
  apply @boundary_extension_family_measurable Ω hτ.measurableSpace
    (fun ω z => F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ))) fbar
    _ hext'
  intro z hz
  exact (continuous_eval_const (⟨z, hz⟩ : upperHalfPlane)).measurable.comp
    (source_stopped_inversePath_measurable B hm hc κ γ G F hw τ hτ)

end SLEExactGauge

end

end OAI

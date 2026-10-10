import OAI.Probability.SLE.StoppedMeasures
import OAI.Probability.SLE.InteriorDiskProof

namespace OAI

/-!
Equality of actual continuous SLE trace laws under capacity scaling. The
Brownian driver laws agree by finite-dimensional uniqueness. Canonical
reverse-flow approximants transfer the measurable trace factor through that
law equality, so no scaling law for geometric events is assumed.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.ScaleTraceLaw

local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem brownian_continuous_path_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B B' : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hm : ∀ t, Measurable (B t)) (hm' : ∀ t, Measurable (B' t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hc' : ∀ ω, Continuous (fun t => B' t ω)) :
    P.map (sourceDriverPath B hc) = P.map (sourceDriverPath B' hc') := by
  have hb : Measurable (fun ω t => B t ω) := Measurable.of_eval hm
  have hb' : Measurable (fun ω t => B' t ω) := Measurable.of_eval hm'
  have hleft : IsProjectiveLimit (P.map (fun ω t => B t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hb]
    exact (hB.hasLaw I).map_eq
  have hright : IsProjectiveLimit (P.map (fun ω t => B' t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hb']
    exact (hB'.hasLaw I).map_eq
  have he := congrArg (Measure.map (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)))
    (hleft.unique hright)
  have hem : Measurable (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [Measure.map_map hem hb, Measure.map_map hem hb'] at he
  apply source_path_evaluation_embedding.map_injective
  rw [Measure.map_map source_path_evaluation_embedding.measurable
      (source_path_measurable _ hm),
    Measure.map_map source_path_evaluation_embedding.measurable (source_path_measurable _ hm')]
  exact he

/-- Equality of continuous driver laws gives equality of the actual trace
laws. Reverse-flow approximants identify the trace factor on the common law. -/
theorem trace_path_law_of_driver_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B B' : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hm' : ∀ t, Measurable (B' t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hc' : ∀ ω, Continuous (fun t => B' t ω))
    (γ γ' : Ω → ℝ≥0 → ℂ) (G F G' F' : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hw' : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B' t ω) (γ' ω) (G' ω) (F' ω))
    (hlaw : P.map (sourceDriverPath B hc) = P.map (sourceDriverPath B' hc')) :
    P.map (sourceTracePath γ (fun ω => (hw ω).1)) =
      P.map (sourceTracePath γ' (fun ω => (hw' ω).1)) := by
  obtain ⟨Φ, hΦm, hΦ, _⟩ := sourceStoppedTraceLaw κ hκ hκ8 B hB hm hc γ G F hw
  let bp := sourceDriverPath B hc
  let bp' := sourceDriverPath B' hc'
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  let gp' := sourceTracePath γ' (fun ω => (hw' ω).1)
  have hbm : Measurable bp := source_path_measurable _ hm
  have hbm' : Measurable bp' := source_path_measurable _ hm'
  choose Q hQm hQ0 hQd using fun (t : ℝ≥0) (n : ℕ) =>
    source_canonical_reverse_flow κ t (a := 1 / ((n : ℝ) + 1)) (by positivity)
  let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hy : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall ha⟩
  have hlimit (B₀ : ℝ≥0 → Ω → ℝ) (hc₀ : ∀ ω, Continuous (fun t => B₀ t ω))
      (γ₀ : Ω → ℝ≥0 → ℂ) (G₀ F₀ : Ω → ℝ≥0 → ℂ → ℂ)
      (hw₀ : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω)
        (γ₀ ω) (G₀ ω) (F₀ ω)) (ω : Ω) (t : ℝ≥0) :
      Tendsto (fun n => Q t n t (sourceDriverPath B₀ hc₀ ω)) atTop (𝓝 (γ₀ ω t)) := by
    have he (n : ℕ) : Q t n t (sourceDriverPath B₀ hc₀ ω) =
        F₀ ω t ((Real.sqrt κ * B₀ t ω : ℝ) + (a n : ℂ) * Complex.I) := by
      apply (hw₀ ω).reverse_flow_identifies t
        ((Real.sqrt κ * B₀ t ω : ℝ) + (a n : ℂ) * Complex.I) (ha n) (by simp)
        (fun s => Q t n s (sourceDriverPath B₀ hc₀ ω)) (hQ0 t n _)
      intro s hs
      exact (hQd t n _ s hs.1).mono Icc_subset_Ici_self
    have ht := ((hw₀ ω).2.2.2.2.2.2.2.2.2.2.2.2 t).comp hy
    simpa only [he, Function.comp_def] using ht
  have hset (t : ℝ≥0) : MeasurableSet
      {p : C(ℝ≥0, ℝ) | Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0)} :=
    measurableSet_tendsto (𝓝 (0 : ℂ)) (fun n => (hQm t n t).sub
      ((continuous_eval_const t).measurable.comp hΦm))
  have hprime (t : ℝ≥0) : ∀ᵐ ω ∂P, Φ (bp' ω) t = γ' ω t := by
    have ho : ∀ᵐ p ∂P.map bp, Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0) := by
      apply (ae_map_iff hbm.aemeasurable (hset t)).mpr
      exact Eventually.of_forall (fun ω => by
        have hh := hlimit B hc γ G F hw ω t
        have he : Φ (bp ω) t = γ ω t := congrArg (fun p : C(ℝ≥0, ℂ) => p t) (hΦ ω)
        rw [he]
        exact tendsto_sub_nhds_zero_iff.mpr hh)
    rw [hlaw] at ho
    filter_upwards [(ae_map_iff hbm'.aemeasurable (hset t)).mp ho] with ω hω
    exact tendsto_nhds_unique (tendsto_sub_nhds_zero_iff.mp hω) (hlimit B' hc' γ' G' F' hw' ω t)
  have hpath : ∀ᵐ ω ∂P, Φ (bp' ω) = gp' ω := by
    filter_upwards [ae_all_iff.mpr (fun n => hprime (denseSeq ℝ≥0 n))] with ω hω
    apply DFunLike.coe_injective
    exact (denseRange_denseSeq ℝ≥0).equalizer (Φ (bp' ω)).continuous (hw' ω).1
      (funext hω)
  calc
    P.map gp = (P.map bp).map Φ := by
      rw [Measure.map_map hΦm hbm]
      congr 1
      exact funext (fun ω => (hΦ ω).symm)
    _ = (P.map bp').map Φ := by rw [hlaw]
    _ = P.map (Φ ∘ bp') := Measure.map_map hΦm hbm'
    _ = P.map gp' := Measure.map_congr hpath

/-- The actual capacity-normalized scaling on continuous trace paths. -/
def scalePath (c : ℝ≥0) (p : C(ℝ≥0, ℂ)) : C(ℝ≥0, ℂ) :=
  ⟨sourceScaleTrace c p, continuous_const.mul
    (p.continuous.comp (continuous_id.div_const (c ^ 2)))⟩

theorem measurable_scalePath (c : ℝ≥0) : Measurable (scalePath c) :=
  source_path_measurable _ (fun t => measurable_const.mul
    (continuous_eval_const (sourceScaleTime c t)).measurable)

/-- The scaled actual capacity trace has exactly the original path law. -/
theorem scaled_trace_path_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (c : ℝ≥0) (hcpos : 0 < c) :
    P.map (fun ω => scalePath c (sourceTracePath γ (fun ω => (hw ω).1) ω)) =
      P.map (sourceTracePath γ (fun ω => (hw ω).1)) := by
  let Bc : ℝ≥0 → Ω → ℝ := fun t ω => (c : ℝ) * B (sourceScaleTime c t) ω
  have hBc : IsBrownianReal Bc P := by
    have hh := hB.smul (c := (c ^ 2)⁻¹) (inv_ne_zero (pow_ne_zero 2 hcpos.ne'))
    simpa only [Bc, sourceScaleTime, NNReal.coe_inv, NNReal.coe_pow, Real.sqrt_inv,
      Real.sqrt_sq c.coe_nonneg, inv_inv, div_eq_mul_inv, mul_comm] using hh
  have hmc : ∀ t, Measurable (Bc t) := fun t => measurable_const.mul (hm _)
  have hcc : ∀ ω, Continuous (fun t => Bc t ω) := fun ω =>
    continuous_const.mul ((hc ω).comp (continuous_id.div_const (c ^ 2)))
  have hwc : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * Bc t ω)
      (sourceScaleTrace c (γ ω)) (sourceScaleChart c (G ω)) (sourceScaleChart c (F ω)) := by
    intro ω
    have hh := source_scale_witness c hcpos (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω) (hw ω)
    simpa only [Bc, mul_left_comm] using hh
  have hlaw := brownian_continuous_path_law B Bc hB hBc hm hmc hc hcc
  have he := trace_path_law_of_driver_law κ hκ hκ8 B Bc hB hm hmc hc hcc
    γ (fun ω => sourceScaleTrace c (γ ω)) G F (fun ω => sourceScaleChart c (G ω))
    (fun ω => sourceScaleChart c (F ω)) hw hwc hlaw
  exact he.symm

end SLEExactGauge.ScaleTraceLaw

end

end OAI

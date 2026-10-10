import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal

namespace Problem336

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def slopeReadout (z : ℕ → ℝ) : Bool :=
  if (1 / 2 : ℝ) < limsup (fun n : ℕ => z (n + 1) / (n + 1 : ℝ)) atTop
  then true else false

theorem measurable_slopeReadout : Measurable slopeReadout := by
  have h : Measurable (fun z : ℕ → ℝ =>
      limsup (fun n : ℕ => z (n + 1) / (n + 1 : ℝ)) atTop) :=
    Measurable.limsup (fun n => (measurable_pi_apply (n + 1)).div_const _)
  exact Measurable.ite (measurableSet_lt measurable_const h)
    measurable_const measurable_const

theorem slopeReadout_of_tendsto {z : ℕ → ℝ} {b : Bool}
    (h : Tendsto (fun n : ℕ => z (n + 1) / (n + 1 : ℝ)) atTop
      (𝓝 (bitValue b))) :
    slopeReadout z = b := by
  unfold slopeReadout
  rw [h.limsup_eq]
  cases b <;> norm_num [bitValue]

theorem slopeReadout_linear_add_noise (b : Bool) (noise : ℕ → ℝ)
    (hnoise : Tendsto (fun n : ℕ => noise (n + 1) / (n + 1 : ℝ)) atTop (𝓝 0)) :
    slopeReadout (fun n => (n : ℝ) * bitValue b + noise n) = b := by
  apply slopeReadout_of_tendsto
  have h := (tendsto_const_nhds (x := bitValue b) (f := atTop)).add hnoise
  simp only [add_zero] at h
  convert h using 1
  ext n
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  simp [add_div, hn]

theorem brownian_integer_slopes {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => B (n : ℝ≥0) ω / (n : ℝ)) atTop (𝓝 0) := by
  let X : ℕ → Ω → ℝ := fun n ω => B ((n + 1 : ℕ) : ℝ≥0) ω - B (n : ℝ≥0) ω
  have hdist (n : ℕ) :
      nndist (((n + 1 : ℕ) : ℝ≥0) : ℝ) ((n : ℝ≥0) : ℝ) = (1 : ℝ≥0) := by
    apply NNReal.eq
    simp [coe_nndist]
  have hlaw (n : ℕ) : HasLaw (X n) (gaussianReal 0 1) P := by
    have h := hB.hasLaw_sub (((n + 1 : ℕ) : ℝ≥0)) (n : ℝ≥0)
    change HasLaw (X n)
      (gaussianReal 0 (nndist (((n + 1 : ℕ) : ℝ≥0) : ℝ) ((n : ℝ≥0) : ℝ))) P at h
    rw [hdist n] at h
    exact h
  have hindep : iIndepFun X P := hB.hasIndepIncrements.nat Nat.mono_cast
  have hmean : P[X 0] = 0 := by
    rw [(hlaw 0).integral_eq, integral_id_gaussianReal]
  have hstrong := strong_law_ae_real X (hlaw 0).hasGaussianLaw.integrable
    (fun _ _ h => hindep.indepFun h) (fun n => (hlaw n).identDistrib (hlaw 0))
  rw [hmean] at hstrong
  filter_upwards [hstrong, hB.eval_zero_ae_eq_zero] with ω hω hzero
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, X i ω) = B (n : ℝ≥0) ω := by
    simpa only [X, Nat.cast_zero, hzero, sub_zero] using
      Finset.sum_range_sub (fun n : ℕ => B (n : ℝ≥0) ω) n
  simpa only [hsum] using hω

theorem ae_slopeReadout_brownian_observation {I Ω : Type*} [Countable I]
    [MeasurableSpace Ω] {P : Measure Ω} (X : Ω → I → Bool)
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, (fun i => slopeReadout
      (fun n => (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω)) = X ω := by
  have hslopes : ∀ᵐ ω ∂P, ∀ i,
      Tendsto (fun n : ℕ => B i (n : ℝ≥0) ω / (n : ℝ)) atTop (𝓝 0) :=
    ae_all_iff.mpr (fun i => brownian_integer_slopes (hB i))
  filter_upwards [hslopes] with ω hω
  funext i
  apply slopeReadout_linear_add_noise
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_add_atTop_iff_nat 1).mpr (hω i)

def configurationReadout {I : Type*} (z : I → ℕ → ℝ) : I → Bool :=
  fun i => slopeReadout (z i)

theorem measurable_configurationReadout {I : Type*} :
    Measurable (configurationReadout (I := I)) :=
  Measurable.of_eval fun i => measurable_slopeReadout.comp (measurable_pi_apply i)

theorem configurationReadout_reindex {I J : Type*} (f : J → I) (z : I → ℕ → ℝ) :
    configurationReadout (fun j => z (f j)) = fun j => configurationReadout z (f j) := rfl

theorem brownian_observation_readout_hasLaw {I Ω : Type*} [Countable I]
    [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure (I → Bool)}
    (X : Ω → I → Bool) (hX : HasLaw X ν P)
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P) :
    HasLaw (fun ω => configurationReadout
      (fun i (n : ℕ) => (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω)) ν P :=
  hX.congr (ae_slopeReadout_brownian_observation X B hB)

theorem sampler_hasLaw_of_brownian_inversion
    {I Ω W Ω' : Type*} [Countable I]
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {ρ : Measure W} {ν : Measure (I → Bool)}
    {X : Ω → I → Bool} (hX : HasLaw X ν P)
    {B : I → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) P)
    {innovation : Ω → W} (hinnovation : HasLaw innovation ρ P)
    {fresh : Ω' → W} (hfresh : HasLaw fresh ρ P')
    {Z : W → I → ℕ → ℝ} (hZ : Measurable Z)
    (hinverse : ∀ᵐ ω ∂P, Z (innovation ω) =
      fun i (n : ℕ) => (n : ℝ) * bitValue (X ω i) + B i (n : ℝ≥0) ω) :
    HasLaw (fun ω => configurationReadout (Z (fresh ω))) ν P' := by
  have href : HasLaw (fun ω => configurationReadout (Z (innovation ω))) ν P := by
    apply (brownian_observation_readout_hasLaw X hX B hB).congr
    filter_upwards [hinverse] with ω hω
    rw [hω]
  exact HasLaw.comp_of_hasLaw_comp
    (f := fun w : W => configurationReadout (Z w))
    (measurable_configurationReadout.comp hZ).aemeasurable hinnovation hfresh href

end Problem336

end

end OAI

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem336.SlopeReadout

def slope (z : ℕ → ℝ) (n : ℕ) : ℝ :=
  z (n + 1) / (n + 1 : ℕ)

def readout (z : ℕ → ℝ) : Bool :=
  if (1 / 2 : ℝ) < Filter.limsup (slope z) Filter.atTop then true else false

@[fun_prop]
theorem measurable_slope (n : ℕ) : Measurable (fun z : ℕ → ℝ => slope z n) := by
  have h : Measurable (fun z : ℕ → ℝ => z (n + 1)) := measurable_pi_apply _
  exact h.div_const ((n + 1 : ℕ) : ℝ)

@[fun_prop]
theorem measurable_readout : Measurable readout := by
  unfold readout
  exact Measurable.ite
    (measurableSet_lt measurable_const (Measurable.limsup measurable_slope))
    measurable_const measurable_const

theorem readout_of_tendsto {z : ℕ → ℝ} {x : ℝ}
    (hz : Tendsto (slope z) atTop (nhds x)) :
    readout z = if (1 / 2 : ℝ) < x then true else false := by
  unfold readout
  rw [hz.limsup_eq]

theorem readout_of_tendsto_bool {z : ℕ → ℝ} {x : Bool}
    (hz : Tendsto (slope z) atTop (nhds (if x then (1 : ℝ) else 0))) :
    readout z = x := by
  rw [readout_of_tendsto hz]
  cases x <;> norm_num

theorem tendsto_slope_observation {B : ℕ → ℝ} {x : ℝ}
    (hB : Tendsto (slope B) atTop (nhds 0)) :
    Tendsto (slope (fun n => (n : ℝ) * x + B n)) atTop (nhds x) := by
  have heq : slope (fun n => (n : ℝ) * x + B n) =
      fun n => x + slope B n := by
    funext n
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [slope, add_div]
    rw [mul_div_cancel_left₀ x hn]
  rw [heq]
  simpa using tendsto_const_nhds.add hB

theorem readout_observation {B : ℕ → ℝ} (x : Bool)
    (hB : Tendsto (slope B) atTop (nhds 0)) :
    readout (fun n => (n : ℝ) * (if x then 1 else 0) + B n) = x := by
  exact readout_of_tendsto_bool (tendsto_slope_observation hB)

def family {ι : Type*} (z : ι → ℕ → ℝ) : ι → Bool :=
  fun i => readout (z i)

@[fun_prop]
theorem measurable_family {ι : Type*} : Measurable (@family ι) := by
  apply measurable_pi_iff.2
  intro i
  exact measurable_readout.comp (measurable_pi_apply i)

theorem family_reindex {ι κ : Type*} (σ : κ → ι) (z : ι → ℕ → ℝ) :
    family (fun j => z (σ j)) = fun j => family z (σ j) := rfl

theorem family_eq_ae_of_tendsto {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → ι → ℕ → ℝ} {X : Ω → ι → Bool}
    (hY : ∀ i, ∀ᵐ ω ∂P, Tendsto (slope (Y ω i)) atTop
      (nhds (if X ω i then (1 : ℝ) else 0))) :
    (fun ω => family (Y ω)) =ᵐ[P] X := by
  filter_upwards [ae_all_iff.2 hY] with ω hω
  funext i
  exact readout_of_tendsto_bool (hω i)

theorem law_transfer {ι Ω Noise : Type*} [Countable ι]
    [MeasurableSpace Ω] [MeasurableSpace Noise]
    {P : Measure Ω} {μ : Measure Noise}
    {W : Ω → Noise} {Z : Noise → ι → ℕ → ℝ}
    {Y : Ω → ι → ℕ → ℝ} {X : Ω → ι → Bool}
    (hW : Measurable W) (hZ : Measurable Z) (hLaw : P.map W = μ)
    (hDecoder : (fun ω => Z (W ω)) =ᵐ[P] Y)
    (hSlopes : ∀ i, ∀ᵐ ω ∂P, Tendsto (slope (Y ω i)) atTop
      (nhds (if X ω i then (1 : ℝ) else 0))) :
    μ.map (fun w => family (Z w)) = P.map X := by
  rw [← hLaw]
  change (P.map W).map (family ∘ Z) = P.map X
  rw [Measure.map_map (measurable_family.comp hZ) hW]
  apply Measure.map_congr
  filter_upwards [hDecoder, family_eq_ae_of_tendsto hSlopes] with ω hD hS
  change family (Z (W ω)) = X ω
  rw [hD]
  exact hS

theorem law_transfer_observation {ι Ω Noise : Type*} [Countable ι]
    [MeasurableSpace Ω] [MeasurableSpace Noise]
    {P : Measure Ω} {μ : Measure Noise}
    {W : Ω → Noise} {Z : Noise → ι → ℕ → ℝ}
    {B : Ω → ι → ℕ → ℝ} {X : Ω → ι → Bool}
    (hW : Measurable W) (hZ : Measurable Z) (hLaw : P.map W = μ)
    (hDecoder : (fun ω => Z (W ω)) =ᵐ[P]
      (fun ω i n => (n : ℝ) * (if X ω i then 1 else 0) + B ω i n))
    (hNoise : ∀ i, ∀ᵐ ω ∂P, Tendsto (slope (B ω i)) atTop (nhds 0)) :
    μ.map (fun w => family (Z w)) = P.map X := by
  apply law_transfer hW hZ hLaw hDecoder
  intro i
  filter_upwards [hNoise i] with ω hω
  exact tendsto_slope_observation hω

end Problem336.SlopeReadout

end

end OAI

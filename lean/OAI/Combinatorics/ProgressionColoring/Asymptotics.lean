import OAI.Combinatorics.ProgressionColoring.Parameters
import OAI.Combinatorics.ProgressionColoring.GenericAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

namespace OAI

/-!
# Absolute thresholds for the construction

The eventual assertions here concern natural progression lengths only.  In
particular, their thresholds are chosen before any number of colors is supplied.
-/

noncomputable section

open Filter Topology

namespace QuantitativeVanDerWaerden.Parameters

/-- A convenient finite list of stronger scale inequalities.  Existence is
proved below from the actual parameter definitions. -/
structure BasicScales (k : ℕ) : Prop where
  length_large : 1000 ≤ k
  dimension_large : (1000 : ℝ) ≤ dimension k
  cutoff_small : (cutoff k : ℝ) ≤ (k : ℝ) / 100
  dimension_cutoff_small : (dimension k : ℝ) * cutoff k ≤ k
  short_period_gap : (dimension k : ℝ) ^ 2 < 2 * cutoff k
  flip_small : flipProbability k < 1 / 2

theorem dimension_tendsto :
    Tendsto (fun k : ℕ => (dimension k : ℝ)) atTop atTop := by
  exact tendsto_atTop_mono dimension_lower
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop)

theorem cutoff_tendsto :
    Tendsto (fun k : ℕ => (cutoff k : ℝ)) atTop atTop := by
  exact tendsto_atTop_mono cutoff_lower
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop)

theorem flipProbability_tendsto : Tendsto flipProbability atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => (k : ℝ) ^ (-1 / 20 : ℝ)) atTop (𝓝 0)
  simpa only [Function.comp_def, neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)

theorem eventually_basicScales : ∀ᶠ k : ℕ in atTop, BasicScales k := by
  have hM := Scaling.eventually_rpow_le
    (a := (1 / 2 : ℝ)) (b := 1) (C := 2) (eps := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  have hDM := Scaling.eventually_rpow_le
    (a := (3 / 5 : ℝ)) (b := 1) (C := 4) (eps := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have hD2 := Scaling.eventually_rpow_le
    (a := (1 / 5 : ℝ)) (b := 1 / 2) (C := 4) (eps := 1)
    (by norm_num) (by norm_num) (by norm_num)
  have hD := dimension_tendsto.eventually (eventually_ge_atTop (1000 : ℝ))
  have hp := flipProbability_tendsto.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 1000, hM, hDM, hD2, hD, hp]
    with k hk hM hDM hD2 hD hp
  have hk1 : 1 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine ⟨hk, hD, ?_, ?_, ?_, hp⟩
  · have := (cutoff_upper hk1).trans hM
    simpa [Real.rpow_one, div_eq_mul_inv, mul_comm] using this
  · have := (dimension_cutoff_upper hk1).trans hDM
    simpa using this
  · have hu := (dimension_sq_upper hk1).trans hD2
    have hl := cutoff_lower k
    have ht := Real.rpow_pos_of_pos hk0 (1 / 2 : ℝ)
    nlinarith

theorem exists_basicScales_threshold : ∃ K : ℕ, ∀ k ≥ K, BasicScales k :=
  eventually_atTop.1 eventually_basicScales

/-- All elementary small-mesh inequalities used in the geometric dichotomy. -/
structure GeometryScales (k : ℕ) : Prop where
  two_cutoff_le_length : 2 * (cutoff k : ℝ) ≤ k
  affine_box : 2 * k * meshScale k < 1
  return_error : 6 * cutoff k * meshScale k / k < 1
  rational_separation : 4 * cutoff k * meshScale k < 1 / 2
  lattice_separation : 2 * meshScale k + 4 * cutoff k * meshScale k < 1
  mesh_lift : 2 * meshScale k * (k + 1) < 1
  cut_error : 4 * cutoff k * meshScale k / k < cutScale k
  cut_small : 4 * cutScale k < 1
  regular_fraction : (4 / 1000 : ℝ) + 1 / dimension k < 1 / 2
  block_loss : 2 * (cutoff k : ℝ) / k ≤ 1 / 16
  heavy_return : 2 * (cutoff k : ℝ) ≤ (k : ℝ) / 10
  light_row_size : (100 : ℝ) ≤ (cutoff k : ℝ) / 10 - 1
  local_event_size : (100 : ℝ) ≤ (dimension k : ℝ) ^ 2 / 2

theorem geometryScales_of_basic {k : ℕ} (h : BasicScales k)
    (hM : (1010 : ℝ) ≤ cutoff k) : GeometryScales k := by
  have hk : (1000 : ℝ) ≤ k := by exact_mod_cast h.length_large
  have hk0 : (0 : ℝ) < k := by linarith
  have hd : (1000 : ℝ) ≤ dimension k := h.dimension_large
  have hd0 : (0 : ℝ) < dimension k := by linarith
  have hm := h.cutoff_small
  have hdm := h.dimension_cutoff_small
  have hk2 : (1000000 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk3 : 4000 * (k : ℝ) < (k : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hk2 hk0.le
    nlinarith
  constructor
  · linarith
  · unfold meshScale
    field_simp
    nlinarith
  · unfold meshScale
    apply (div_lt_iff₀ hk0).2
    field_simp
    nlinarith
  · unfold meshScale
    field_simp
    nlinarith
  · unfold meshScale
    field_simp
    nlinarith
  · unfold meshScale
    field_simp
    nlinarith
  · unfold meshScale cutScale
    apply (div_lt_div_iff₀ hk0 (by positivity : 0 < 1000 * (dimension k : ℝ))).2
    field_simp
    nlinarith
  · unfold cutScale
    field_simp
    nlinarith
  · have hinv : 1 / (dimension k : ℝ) < 1 / 4 :=
      (div_lt_iff₀ hd0).2 (by linarith)
    linarith
  · apply (div_le_iff₀ hk0).2
    linarith
  · linarith
  · linarith
  · nlinarith

theorem eventually_geometryScales : ∀ᶠ k : ℕ in atTop, GeometryScales k := by
  filter_upwards [eventually_basicScales,
    cutoff_tendsto.eventually (eventually_ge_atTop (1010 : ℝ))] with k hk hM
  exact geometryScales_of_basic hk hM

theorem exists_geometryScales_threshold : ∃ K : ℕ, ∀ k ≥ K, GeometryScales k :=
  eventually_atTop.1 eventually_geometryScales

end QuantitativeVanDerWaerden.Parameters

end

end OAI

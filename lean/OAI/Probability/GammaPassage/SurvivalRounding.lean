import OAI.Probability.GammaPassage.SurvivalQuantile
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Int
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace OAI

namespace GammaFPP
open Set Filter
open scoped Topology ENNReal
variable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)

noncomputable def gammaRoundedSurvival (t : ℕ) (x : ℝ) : ℝ :=
  (⌊(2 : ℝ)^t * gammaSurvival shape rate x⌋₊ : ℝ) / (2 : ℝ)^t

noncomputable def gammaRoundedCost (t : ℕ) (x : ℝ) : ℝ :=
  gammaSurvivalQuantile hs hr (gammaRoundedSurvival (shape := shape) (rate := rate) t x)

lemma gammaRoundedSurvival_nonneg (t : ℕ) (x : ℝ) :
    0 ≤ gammaRoundedSurvival (shape := shape) (rate := rate) t x := by
  unfold gammaRoundedSurvival
  positivity

lemma gammaRoundedSurvival_le (hs : 0 < shape) (hr : 0 < rate) (t : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gammaRoundedSurvival (shape := shape) (rate := rate) t x ≤ gammaSurvival shape rate x := by
  rw [gammaRoundedSurvival, div_le_iff₀ (by positivity)]
  have hp := (gammaSurvival_mem hs hr hx).1.le
  simpa only [mul_comm] using Nat.floor_le
    (show 0 ≤ (2 : ℝ)^t * gammaSurvival shape rate x by positivity)

lemma gammaRoundedSurvival_tendsto (hs : 0 < shape) (hr : 0 < rate) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun t => gammaRoundedSurvival (shape := shape) (rate := rate) t x)
      atTop (𝓝 (gammaSurvival shape rate x)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (gammaSurvival_mem hs hr hx).1.le).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  simpa [gammaRoundedSurvival, Function.comp_def, mul_comm] using h

lemma gammaRoundedSurvival_eventually_pos (hs : 0 < shape) (hr : 0 < rate) {x : ℝ} (hx : 0 ≤ x) :
    ∀ᶠ t in atTop, 0 < gammaRoundedSurvival (shape := shape) (rate := rate) t x :=
  (gammaRoundedSurvival_tendsto hs hr hx).eventually
    (lt_mem_nhds (gammaSurvival_mem hs hr hx).1)

lemma gammaRoundedCost_ge (t : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hp : 0 < gammaRoundedSurvival (shape := shape) (rate := rate) t x) :
    x ≤ gammaRoundedCost hs hr t x :=
  gammaSurvivalQuantile_upper_cost hs hr hx hp (gammaRoundedSurvival_le hs hr t hx)

lemma gammaRoundedCost_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun t => gammaRoundedCost hs hr t x) atTop (𝓝 x) := by
  have hS := gammaSurvival_mem hs hr hx
  have hw : Tendsto (fun t => gammaRoundedSurvival (shape := shape) (rate := rate) t x)
      atTop (𝓝[Ioc (0 : ℝ) 1] (gammaSurvival shape rate x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨gammaRoundedSurvival_tendsto hs hr hx, ?_⟩
    filter_upwards [gammaRoundedSurvival_eventually_pos hs hr hx] with t ht
    exact ⟨ht, (gammaRoundedSurvival_le hs hr t hx).trans hS.2⟩
  have h := ((gammaSurvivalQuantile_continuousOn hs hr) _ hS).tendsto.comp hw
  simpa only [gammaSurvivalQuantile_inverse hs hr hx, gammaRoundedCost,
    Function.comp_def] using h

/-- Every finite-bit scalar decoder has the intended extended meaning.
In particular the zero rank is infinite, even though the real totalization is zero. -/
lemma gammaRoundedSurvival_finite_iff (t : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gammaSurvivalQuantileExtended hs hr
      (gammaRoundedSurvival (shape := shape) (rate := rate) t x) ≠ ⊤ ↔
    0 < gammaRoundedSurvival (shape := shape) (rate := rate) t x := by
  apply gammaSurvivalQuantileExtended_ne_top_iff hs hr
  exact ⟨gammaRoundedSurvival_nonneg t x,
    (gammaRoundedSurvival_le hs hr t hx).trans (gammaSurvival_mem hs hr hx).2⟩
end GammaFPP

end OAI

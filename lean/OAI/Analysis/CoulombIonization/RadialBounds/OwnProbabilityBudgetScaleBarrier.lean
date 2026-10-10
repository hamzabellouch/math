import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ActualPosteriorCapBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma own_probability_log_cost_tendsto {v : ℝ} (hv : 0 < v) :
    Tendsto (fun p : ℝ => p^v*(Real.log (Real.exp 1/p))^5)
      (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ := v/5
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : Tendsto (fun p : ℝ => p^q) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero hq).mono_left inf_le_left
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hq
  have hh := (hpow.sub hlog).pow 5
  simp only [sub_zero,zero_pow (by norm_num : (5:ℕ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
  rw [Real.log_div (Real.exp_pos 1).ne' hp.ne',Real.log_exp]
  rw [show p^q-Real.log p*p^q = p^q*(1-Real.log p) by ring,
    mul_pow,←Real.rpow_natCast,←Real.rpow_mul hp.le]
  congr 2
  dsimp [q]
  ring

lemma own_probability_weighted_budget_tendsto {ι : Type*} {l : Filter ι}
    {r p : ι → ℝ} {v δ : ℝ} (hr : ∀ᶠ i in l, 0 < r i)
    (hr0 : Tendsto r l (𝓝 0)) (hp : ∀ᶠ i in l, 0 < p i)
    (hp0 : Tendsto p l (𝓝 0)) (hv : 2.02 < v) :
    Tendsto (fun i => (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ*(r i)^v)
      l (𝓝 0) := by
  have hlog := (own_probability_log_cost_tendsto (by norm_num : (0:ℝ) < 1/4)).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hp0,hp⟩)
  have hrp := hr0.rpow_const_nhds_zero (by linarith : 0 < v-2.02)
  have hrp' := hr0.rpow_const_nhds_zero (by linarith : 0 < v)
  have hpp := hp0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/4)
  have hh := ((hlog.mul hrp).const_mul observationFisherConstant).add
    ((hpp.mul hrp').const_mul δ)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [hr] with i hi
  have he : (r i)^(-2.02:ℝ)*(r i)^v = (r i)^(v-2.02) := by
    rw [←Real.rpow_add hi]
    congr 1
    ring
  dsimp only [dyadicUniformEventBudget]
  rw [show (p i)^(1/4:ℝ)*
    (observationFisherConstant*(r i)^(-2.02:ℝ)*(Real.log (Real.exp 1/p i))^5+δ)*(r i)^v =
      observationFisherConstant*((p i)^(1/4:ℝ)*(Real.log (Real.exp 1/p i))^5)*
        ((r i)^(-2.02:ℝ)*(r i)^v)+δ*((p i)^(1/4:ℝ)*(r i)^v) by ring,he]
  dsimp only [Function.comp_apply]
  ring

theorem own_probability_band_excess_tendsto {ι : Type*} {l : Filter ι}
    {r p : ι → ℝ} {y : ι → Space} {w δ : ℝ}
    (hr : ∀ᶠ i in l, 0 < r i) (hr0 : Tendsto r l (𝓝 0))
    (hp : ∀ᶠ i in l, 0 < p i) (hp0 : Tendsto p l (𝓝 0))
    (hy : ∀ᶠ i in l, ‖y i‖ ≤ 2*r i) (hw : w < 1/10) (hδ : 0 ≤ δ) :
    Tendsto (fun i => (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ*
      (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  have he := own_probability_weighted_budget_tendsto hr hr0 hp hp0 (δ := δ)
    (by linarith : (2.02:ℝ) < 7-w)
  have hn : ∀ᶠ i in l, 0 ≤ (p i)^(1/4:ℝ)*dyadicUniformEventBudget (r i) (p i) δ := by
    filter_upwards [hr,hp,hp0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi hpi hpi1
    exact mul_nonneg (Real.rpow_nonneg hpi.le _)
      (dyadicUniformEventBudget_nonneg hi hpi hpi1.le hδ)
  apply squeeze_zero' _ _ he
  · filter_upwards [hn] with i hi
    exact mul_nonneg hi (Real.rpow_nonneg (by unfold localCellRadius; positivity) _)
  · filter_upwards [hr,hy,hn] with i hi hyi hni
    apply mul_le_mul_of_nonneg_left _ hni
    apply Real.rpow_le_rpow (by unfold localCellRadius; positivity) _ (by linarith)
    unfold localCellRadius
    linarith

end CoulombAtom

end

end OAI

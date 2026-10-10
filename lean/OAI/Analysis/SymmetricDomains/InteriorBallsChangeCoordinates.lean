import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology NNReal

theorem interior_balls_change_coordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph E F) (hem : (0 : E) ∈ e.source) (he0 : e 0 = 0)
    (he : ContDiffAt ℝ 1 e 0) (hei : ContDiffAt ℝ 1 e.symm 0)
    {Ω : Set E} {c C t₀ : ℝ} (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hballs : ∀ t, 0 < t → t < t₀ → ∃ a : E, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω) :
    ∃ d D t₁ : ℝ, 0 < d ∧ 0 < D ∧ 0 < t₁ ∧ ∀ t, 0 < t → t < t₁ →
      ∃ b : F, ‖b‖ ≤ D*t ∧ ball b (d*t) ⊆ e '' (Ω ∩ e.source) := by
  obtain ⟨L,S,hS,hL⟩ := he.exists_lipschitzOnWith
  obtain ⟨K,T,hT,hK⟩ := hei.exists_lipschitzOnWith
  have htar : (0 : F) ∈ e.target := he0 ▸ e.map_source hem
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hS (e.open_source.mem_nhds hem))
  obtain ⟨R,hR,hRt⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hT (e.open_target.mem_nhds htar))
  let d : ℝ := c/((K:ℝ)+1)
  let D : ℝ := ((L:ℝ)+1)*C
  have hKp : 0 < (K:ℝ)+1 := by positivity
  have hLp : 0 < (L:ℝ)+1 := by positivity
  have hd : 0 < d := div_pos hc hKp
  have hD : 0 < D := mul_pos hLp hC
  let t₁ := min t₀ (min (r/(C+1)) (R/(D+d+1)))
  have ht₁ : 0 < t₁ := lt_min ht₀ (lt_min (div_pos hr (by positivity)) (div_pos hR (by positivity)))
  refine ⟨d,D,t₁,hd,hD,ht₁,?_⟩
  intro t ht htt
  have htt₀ : t < t₀ := htt.trans_le (min_le_left _ _)
  have htr : t < r/(C+1) := (htt.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have htR : t < R/(D+d+1) := (htt.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hCr : C*t < r := by
    have hh := (lt_div_iff₀ (by positivity : 0 < C+1)).mp htr
    nlinarith
  have hDR : D*t+d*t < R := by
    have hh := (lt_div_iff₀ (by positivity : 0 < D+d+1)).mp htR
    nlinarith
  obtain ⟨a,ha,haball⟩ := hballs t ht htt₀
  have har : a ∈ ball (0 : E) r := mem_ball_zero_iff.mpr (ha.trans_lt hCr)
  have has : a ∈ e.source := (hrs har).2
  have hLa : ‖e a‖ ≤ (L:ℝ)*‖a‖ := by
    simpa only [he0,dist_zero_right] using
      hL.dist_le_mul a (hrs har).1 0 (hrs (mem_ball_self hr)).1
  have heb : ‖e a‖ ≤ D*t := by
    calc ‖e a‖ ≤ (L:ℝ) * ‖a‖ := hLa
         _ ≤ (L:ℝ)*(C*t) := mul_le_mul_of_nonneg_left ha L.coe_nonneg
         _ ≤ D*t := by dsimp [D]; nlinarith [L.coe_nonneg]
  have hear : e a ∈ ball (0 : F) R := mem_ball_zero_iff.mpr (heb.trans_lt (by nlinarith))
  refine ⟨e a,heb,?_⟩
  intro y hy
  have hyr : y ∈ ball (0 : F) R := by
    apply mem_ball_zero_iff.mpr
    have hn : ‖y‖ ≤ dist y (e a)+‖e a‖ := by
      simpa only [dist_zero_right] using dist_triangle y (e a) 0
    have hd' : dist y (e a) < d*t := hy
    linarith
  have hyt : y ∈ e.target := (hRt hyr).2
  have hpre : e.symm y ∈ ball a (c*t) := by
    have hdist : dist (e.symm y) a ≤ (K:ℝ) * dist y (e a) := by
      simpa only [e.left_inv has] using
        hK.dist_le_mul y (hRt hyr).1 (e a) (hRt hear).1
    have hd' : dist y (e a) < d*t := hy
    have hprod : ((K:ℝ)+1)*(d*t) = c*t := by dsimp [d]; field_simp
    have hlt : (K:ℝ)*dist y (e a) < c*t := by
      calc (K:ℝ)*dist y (e a) ≤ ((K:ℝ)+1)*dist y (e a) := by nlinarith [dist_nonneg (x:=y) (y:=e a)]
           _ < ((K:ℝ)+1)*(d*t) := mul_lt_mul_of_pos_left hd' hKp
           _ = c*t := hprod
    exact hdist.trans_lt hlt
  exact ⟨e.symm y,⟨haball hpre,e.map_target hyt⟩,e.right_inv hyt⟩

end Release061

end

end OAI

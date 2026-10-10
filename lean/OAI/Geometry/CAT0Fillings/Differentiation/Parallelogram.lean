import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.TwoPoint
import OAI.Geometry.CAT0Fillings.Differentiation.Density
import OAI.Geometry.CAT0Fillings.Geometry.Comparison

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
section MetricDifferential
variable {X : Type*} [MetricSpace X]
omit [MeasurableSpace E] [BorelSpace E] in

lemma HasTwoPointMetricDifferential.scaled_pair_limit
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x u v : E}
    (h : HasTwoPointMetricDifferential f p s x)
    {c : ℕ → ℝ} {d e : ℕ → E}
    (hc : Tendsto (fun j => ‖c j‖) atTop atTop)
    (hd : ∀ᶠ j in atTop, x + d j ∈ s) (he : ∀ᶠ j in atTop, x + e j ∈ s)
    (hcd : Tendsto (fun j => c j • d j) atTop (𝓝 u))
    (hce : Tendsto (fun j => c j • e j) atTop (𝓝 v)) :
    Tendsto (fun j => ‖c j‖ * dist (f (x + d j)) (f (x + e j)))
      atTop (𝓝 (p (u - v))) := by
  have hp := seminorm_continuous_finiteDimensional p
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have he₀ := tangentConeAt.lim_zero atTop hc hce
  have hpair : Tendsto (fun j => (x + d j, x + e j)) atTop (𝓝[s ×ˢ s] (x,x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.add hd₀).prodMk_nhds (tendsto_const_nhds.add he₀)
    · filter_upwards [hd, he] with j hj hj'
      exact ⟨hj, hj'⟩
  have hsmall := h.comp_tendsto hpair
  have hmul := hsmall.mul_isBigO (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => (‖(x + d j) - x‖ + ‖(x + e j) - x‖) * ‖c j‖)
      atTop (𝓝 (‖u‖ + ‖v‖)) := by
    simpa only [norm_smul, add_sub_cancel_left, add_mul, mul_comm] using hcd.norm.add hce.norm
  have hzero := hmul.tendsto_zero_of_tendsto hnorm
  have hdiff := hp.tendsto (u - v) |>.comp (hcd.sub hce)
  have hsum := hzero.add hdiff
  convert hsum using 1
  · ext j
    simp only [Function.comp_apply, add_sub_add_left_eq_sub, ← smul_sub, map_smul_eq_mul]
    ring
  · simp

lemma HasTwoPointMetricDifferential.parallelogram
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x : E}
    (h : HasTwoPointMetricDifferential f p s x) (hX : IsCAT0 X)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (u v : E) :
    p (u + v) ^ 2 + p (u - v) ^ 2 = 2 * p u ^ 2 + 2 * p v ^ 2 := by
  have hle (u v : E) :
      p (u + v) ^ 2 + p (u - v) ^ 2 ≤ 2 * p u ^ 2 + 2 * p v ^ 2 := by
    let z : Fin 4 → E := ![0, u, u + v, v]
    have hz : z ∈ tangentConeAt ℝ {f : Fin 4 → E | ∀ i, f i ∈ s} (fun _ => x) := by
      rw [tangentConeAt_pi_eq_univ_of_density_one μ s x hx]
      exact mem_univ z
    obtain ⟨c, d, hc, hd, hcd⟩ :=
      mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hz
    have hl (i j : Fin 4) :
        Tendsto (fun k => ‖c k‖ * dist (f (x + d k i)) (f (x + d k j)))
          atTop (𝓝 (p (z i - z j))) := by
      apply h.scaled_pair_limit hc
      · filter_upwards [hd] with k hk
        exact hk i
      · filter_upwards [hd] with k hk
        exact hk j
      · exact tendsto_pi_nhds.mp hcd i
      · exact tendsto_pi_nhds.mp hcd j
    have hquad (k : ℕ) :
        (‖c k‖ * dist (f (x + d k 0)) (f (x + d k 2))) ^ 2 +
          (‖c k‖ * dist (f (x + d k 1)) (f (x + d k 3))) ^ 2 ≤
        (‖c k‖ * dist (f (x + d k 0)) (f (x + d k 1))) ^ 2 +
          (‖c k‖ * dist (f (x + d k 1)) (f (x + d k 2))) ^ 2 +
          (‖c k‖ * dist (f (x + d k 2)) (f (x + d k 3))) ^ 2 +
          (‖c k‖ * dist (f (x + d k 3)) (f (x + d k 0))) ^ 2 := by
      have H := hX.quadrilateral (f (x + d k 0)) (f (x + d k 1))
        (f (x + d k 2)) (f (x + d k 3))
      simpa only [mul_add, mul_pow] using mul_le_mul_of_nonneg_left H (sq_nonneg ‖c k‖)
    have H := le_of_tendsto_of_tendsto'
      (((hl 0 2).pow 2).add ((hl 1 3).pow 2))
      (((((hl 0 1).pow 2).add ((hl 1 2).pow 2)).add ((hl 2 3).pow 2)).add
        ((hl 3 0).pow 2)) hquad
    have hneg : p (-u + -v) = p (u + v) := by rw [← neg_add, map_neg_eq_map]
    simpa [z, map_neg_eq_map, hneg, two_mul, add_assoc, add_left_comm, add_comm] using H
  have hf := hle u v
  have hr := hle (u + v) (u - v)
  have he₁ : (u + v) + (u - v) = (2 : ℝ) • u := by module
  have he₂ : (u + v) - (u - v) = (2 : ℝ) • v := by module
  rw [he₁, he₂, map_smul_eq_mul, map_smul_eq_mul] at hr
  norm_num at hr
  linarith

lemma HasTwoPointMetricDifferential.distance_bound
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x : E}
    (h : HasTwoPointMetricDifferential f p s x)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) {A B : ℝ}
    (hAB : ∀ a ∈ s, ∀ b ∈ s, A * dist a b ≤ B * dist (f a) (f b)) (w : E) :
    A * ‖w‖ ≤ B * p w := by
  let z : Fin 2 → E := ![w, 0]
  have hz : z ∈ tangentConeAt ℝ {f : Fin 2 → E | ∀ i, f i ∈ s} (fun _ => x) := by
    rw [tangentConeAt_pi_eq_univ_of_density_one μ s x hx]
    exact mem_univ z
  obtain ⟨c, d, hc, hd, hcd⟩ :=
    mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hz
  have hcd₀ := tendsto_pi_nhds.mp hcd 0
  have hcd₁ := tendsto_pi_nhds.mp hcd 1
  have hl := h.scaled_pair_limit hc (hd.mono fun _ hj => hj 0)
    (hd.mono fun _ hj => hj 1) hcd₀ hcd₁
  have hl' : Tendsto (fun j => ‖c j‖ * dist (f (x + d j 0)) (f (x + d j 1)))
      atTop (𝓝 (p w)) := by simpa [z] using hl
  have hr : Tendsto (fun j => ‖c j‖ * dist (x + d j 0) (x + d j 1))
      atTop (𝓝 ‖w‖) := by
    simpa only [Pi.smul_apply, dist_eq_norm, add_sub_add_left_eq_sub, ← norm_smul, smul_sub,
      z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero]
      using (hcd₀.sub hcd₁).norm
  apply le_of_tendsto_of_tendsto (hr.const_mul A) (hl'.const_mul B)
  filter_upwards [hd] with j hj
  have H := mul_le_mul_of_nonneg_left
    (hAB (x + d j 0) (hj 0) (x + d j 1) (hj 1)) (norm_nonneg (c j))
  simpa only [mul_left_comm] using H

end MetricDifferential
end CAT0Fillings

namespace CAT0Fillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {X : Type*} [MetricSpace X]

lemma HasTwoPointMetricDifferential.parallelogram_of_quadrilateralOn
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x : E}
    (h : HasTwoPointMetricDifferential f p s x)
    (hQ : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (f a) (f c)^2 + dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2 + dist (f b) (f c)^2 + dist (f c) (f d)^2 + dist (f d) (f a)^2)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (u v : E) :
    p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2 := by
  have hle (u v : E) : p (u+v)^2+p (u-v)^2 ≤ 2*p u^2+2*p v^2 := by
    let z : Fin 4 → E := ![0,u,u+v,v]
    have hz : z ∈ tangentConeAt ℝ {f : Fin 4 → E | ∀ i, f i ∈ s} (fun _ => x) := by
      rw [tangentConeAt_pi_eq_univ_of_density_one μ s x hx]
      exact mem_univ z
    obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hz
    have hl (i j : Fin 4) :
        Tendsto (fun k => ‖c k‖*dist (f (x+d k i)) (f (x+d k j))) atTop (𝓝 (p (z i-z j))) := by
      apply h.scaled_pair_limit hc
      · filter_upwards [hd] with k hk
        exact hk i
      · filter_upwards [hd] with k hk
        exact hk j
      · exact tendsto_pi_nhds.mp hcd i
      · exact tendsto_pi_nhds.mp hcd j
    have hquad : ∀ᶠ k in atTop,
        (‖c k‖*dist (f (x+d k 0)) (f (x+d k 2)))^2 +
        (‖c k‖*dist (f (x+d k 1)) (f (x+d k 3)))^2 ≤
        (‖c k‖*dist (f (x+d k 0)) (f (x+d k 1)))^2 +
        (‖c k‖*dist (f (x+d k 1)) (f (x+d k 2)))^2 +
        (‖c k‖*dist (f (x+d k 2)) (f (x+d k 3)))^2 +
        (‖c k‖*dist (f (x+d k 3)) (f (x+d k 0)))^2 := by
      filter_upwards [hd] with k hk
      have H := hQ _ (hk 0) _ (hk 1) _ (hk 2) _ (hk 3)
      simpa only [Pi.add_apply,mul_add,mul_pow] using mul_le_mul_of_nonneg_left H (sq_nonneg ‖c k‖)
    have H := le_of_tendsto_of_tendsto
      (((hl 0 2).pow 2).add ((hl 1 3).pow 2))
      (((((hl 0 1).pow 2).add ((hl 1 2).pow 2)).add ((hl 2 3).pow 2)).add ((hl 3 0).pow 2)) hquad
    have hneg : p (-u+-v) = p (u+v) := by rw [←neg_add,map_neg_eq_map]
    simpa [z,map_neg_eq_map,hneg,two_mul,add_assoc,add_left_comm,add_comm] using H
  have hf := hle u v
  have hr := hle (u+v) (u-v)
  have he₁ : (u+v)+(u-v) = (2 : ℝ) • u := by module
  have he₂ : (u+v)-(u-v) = (2 : ℝ) • v := by module
  rw [he₁,he₂,map_smul_eq_mul,map_smul_eq_mul] at hr
  norm_num at hr
  linarith
end CAT0Fillings

end

end OAI

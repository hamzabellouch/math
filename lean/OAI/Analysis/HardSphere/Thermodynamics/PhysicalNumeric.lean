import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalSupported
import OAI.Analysis.HardSphere.Collisions.PhysicalCollision

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

lemma choose_physical_group {p κ B : ℝ} (hp : 0<p) (hκ : 0<κ) (_hB : 1≤B) :
    ∃q : ℕ,0<q ∧ (2/5:ℝ)^q≤p/2 ∧
      ∃δ : ℝ,0<δ ∧ δ<1 ∧ 2*(B-1)/(2*q:ℝ)-8*Real.log δ≤κ := by
  let δ := Real.exp (-κ/32)
  have hδ : 0<δ := Real.exp_pos _
  have hδ1 : δ<1 := by dsimp only [δ]; rw [Real.exp_lt_one_iff]; linarith
  have hpow : Tendsto (fun q : ℕ ↦ (2/5:ℝ)^q) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hdiv : Tendsto (fun q : ℕ ↦ 2*(B-1)/(2*q:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2))
  obtain ⟨q,hq,hpow,hdiv⟩ := Filter.Eventually.exists (
    (eventually_ge_atTop (1:ℕ)).and ((hpow.eventually (gt_mem_nhds (by positivity : (0:ℝ)<p/2))).and
      (hdiv.eventually (gt_mem_nhds (by linarith : (0:ℝ)<κ/2)))))
  refine ⟨q,by omega,hpow.le,δ,hδ,hδ1,?_⟩
  dsimp only [δ]
  rw [Real.log_exp]
  linarith

lemma physical_collision_eventually {A t C δ : ℝ} (_hA : 0<A) (ht : 0<t)
    (hC : 0≤C) (hδ : δ<1) (M : ℕ) :
    ∀ᶠ D : ℝ in atTop,∀α : ℝ,0<α → α≤A →
      ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*
        (routeDensityBound t*datumCollisionBound t (α/D) D⁻¹ (D^(1/12:ℝ)) C)≤1 := by
  let J : ℝ≥0∞ := (ENNReal.ofReal (9/10:ℝ)*(ENNReal.ofReal (99/100:ℝ)*midpointLower t 13))⁻¹
  have hJ : J≠⊤ := ENNReal.inv_ne_top.mpr (by
    dsimp only [ne_eq]
    exact mul_ne_zero (by positivity) (mul_ne_zero (by positivity) (midpointLower_pos ht 13).ne'))
  let f := fun D : ℝ ↦ ENNReal.ofReal (hitConstant*
    (4*C*(2*t)*(A/D)+8*(A/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2)))
  have hreal : Tendsto (fun D : ℝ ↦ hitConstant*
    (4*C*(2*t)*(A/D)+8*(A/D)*(1+D^(1/12:ℝ))^3/Real.sqrt (D⁻¹/2))) atTop (𝓝 0) := by
    have hh := ((tendsto_inv_atTop_zero.const_mul (4*C*(2*t)*A)).add
      (boundary_ratio_tendsto.const_mul (8*A))).const_mul hitConstant
    convert hh using 1 <;> try simp only [mul_zero,zero_add]
    funext D
    ring
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [f,Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hlim : Tendsto (fun D ↦ ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*(J*(2*f D))))
      atTop (𝓝 (ENNReal.ofReal δ)) := by
    have hh := ENNReal.Tendsto.const_mul hf (a:=2) (Or.inr (by norm_num))
    have hh := ENNReal.Tendsto.const_mul hh (a:=J) (Or.inr hJ)
    have hh := ENNReal.Tendsto.const_mul hh (a:=routeDensityBound t) (Or.inr (routeDensityBound_ne_top ht))
    have hh := ENNReal.Tendsto.const_mul hh (a:=(4*(49^3*(M+1)):ℕ)) (Or.inr (by finiteness))
    simpa only [mul_zero,add_zero] using tendsto_const_nhds.add hh
  have hδE : ENNReal.ofReal δ<1 := ENNReal.ofReal_lt_one.mpr hδ
  filter_upwards [eventually_ge_atTop (1:ℝ),hlim.eventually (gt_mem_nhds hδE)] with D hD hh
  intro α hα hαA
  refine le_trans ?_ hh.le
  gcongr
  change J*(2*ENNReal.ofReal _)≤J*(2*f D)
  gcongr
  dsimp only [f]
  apply ENNReal.ofReal_le_ofReal
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hhit : 0≤hitConstant := le_of_lt hitConstant_pos
  gcongr

end HardSphere.Groups
end
end

end OAI

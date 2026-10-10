import Mathlib
import OAI.Analysis.SymmetricDomains.EventualOffsetBall

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

lemma complex_re_norm_le {k : ℕ} (a : Fin k → ℂ) : ‖fun i => (a i).re‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (RCLike.norm_re_le_norm (a i)).trans (norm_le_pi_norm a i)

lemma complex_im_norm_le {k : ℕ} (a : Fin k → ℂ) : ‖fun i => (a i).im‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (RCLike.norm_im_le_norm (a i)).trans (norm_le_pi_norm a i)

theorem complex_balls_to_normal_offsets {k : ℕ} {Ω : Set (Fin k → ℂ)}
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0)
    {ρ c C t₀ : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hballs : ∀ t, 0 < t → t < t₀ → ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω) :
    ∃ D t₁ : ℝ, 0 < D ∧ 0 < t₁ ∧ ∀ t, 0 < t → t < t₁ →
      ∃ x v : Fin k → ℝ, ‖x‖ ≤ C*t ∧ ‖v‖ ≤ D*t ∧
        ball v (c*t) ⊆ {u | ‖u‖ < ρ ∧
          (fun i => (x i : ℂ)+Complex.I*((φ x i+u i) : ℂ)) ∈ Ω} := by
  obtain ⟨K,S,hS,hK⟩ := hφ.exists_lipschitzOnWith
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hS
  let D : ℝ := (1+(K:ℝ))*C
  have hD : 0 < D := mul_pos (by positivity) hC
  let t₁ := min t₀ (min (r/(C+1)) (ρ/(D+c+1)))
  have ht₁ : 0 < t₁ := lt_min ht₀ (lt_min (div_pos hr (by positivity)) (div_pos hρ (by positivity)))
  refine ⟨D,t₁,hD,ht₁,?_⟩
  intro t ht htt
  have htt₀ : t < t₀ := htt.trans_le (min_le_left _ _)
  have htr : t < r/(C+1) := (htt.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have htρ : t < ρ/(D+c+1) := (htt.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hCr : C*t < r := by
    have hh := (lt_div_iff₀ (by positivity : 0 < C+1)).mp htr
    nlinarith
  have hDr : D*t+c*t < ρ := by
    have hh := (lt_div_iff₀ (by positivity : 0 < D+c+1)).mp htρ
    nlinarith
  obtain ⟨a,ha,hab⟩ := hballs t ht htt₀
  let x : Fin k → ℝ := fun i => (a i).re
  let v : Fin k → ℝ := (fun i => (a i).im)-φ x
  have hx : ‖x‖ ≤ C*t := (complex_re_norm_le a).trans ha
  have hxS : x ∈ S := hrs (mem_ball_zero_iff.mpr (hx.trans_lt hCr))
  have hφb : ‖φ x‖ ≤ (K:ℝ)*‖x‖ := by
    simpa only [hφ0,dist_zero_right] using hK.dist_le_mul x hxS 0 (mem_of_mem_nhds hS)
  have hv : ‖v‖ ≤ D*t := by
    calc ‖v‖ ≤ ‖fun i => (a i).im‖+‖φ x‖ := norm_sub_le _ _
         _ ≤ C*t+(K:ℝ)*(C*t) := add_le_add ((complex_im_norm_le a).trans ha)
           (hφb.trans (mul_le_mul_of_nonneg_left hx K.coe_nonneg))
         _ = D*t := by dsimp [D]; ring
  refine ⟨x,v,hx,hv,?_⟩
  intro u hu
  refine ⟨?_,complex_ball_offset_ball φ hab hu⟩
  have hh : ‖u-v‖ < c*t := by simpa only [mem_ball,dist_eq_norm] using hu
  calc ‖u‖ ≤ ‖u-v‖+‖v‖ := norm_le_norm_sub_add _ _
       _ < c*t+D*t := add_lt_add_of_lt_of_le hh hv
       _ < ρ := by linarith

theorem normal_offset_noncollapse {k : ℕ} {Ω : Set (Fin k → ℂ)}
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0)
    {ρ c C t₀ : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hballs : ∀ t, 0 < t → t < t₀ → ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω)
    (hbdry : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      (fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ)) ∉ Ω)
    (F : Set (Fin k → ℝ))
    (hexcluded : ∀ (s : ℕ → Fin k → ℝ) (t : ℕ → ℝ) (v : ℕ → Fin k → ℝ) (w : Fin k → ℝ),
      Tendsto s atTop (𝓝 0) → Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
      Tendsto v atTop (𝓝 w) → w ∈ F →
      Tendsto (fun j => infDist (v j)
        (offsetScaled (fun x => {u | ‖u‖ < ρ ∧
          (fun i => (x i : ℂ)+Complex.I*((φ x i+u i) : ℂ)) ∈ Ω}) (s j) (t j))ᶜ)
        atTop (𝓝 0)) : F ≠ univ := by
  obtain ⟨D,t₁,_,ht₁,hfiber⟩ := complex_balls_to_normal_offsets hφ hφ0 hρ hc hC ht₀ hballs
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hbdry
  have hτ : 0 < min t₁ (r/(C+1)) := lt_min ht₁ (div_pos hr (by positivity))
  obtain ⟨t,_,ht,htlim⟩ := exists_seq_strictAnti_tendsto' hτ
  choose x v hx hv hb using fun j => hfiber (t j) (ht j).1 ((ht j).2.trans_le (min_le_left _ _))
  have hxlim : Tendsto x atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) hx
    simpa only [mul_zero] using htlim.const_mul C
  apply excluded_offset_noncollapse _ F hxlim htlim (fun j => (ht j).1) ?_ hc hv hb hexcluded
  intro j hj
  have hxr : ‖x j‖ < r := by
    have hh := (lt_div_iff₀ (by positivity : 0 < C+1)).mp
      ((ht j).2.trans_le (min_le_right _ _))
    nlinarith [hx j,(ht j).1]
  have hh := hrs (mem_ball_zero_iff.mpr hxr)
  apply hh
  simpa only [Pi.zero_apply,Complex.ofReal_zero,add_zero] using hj.2

end Release061

end

end OAI

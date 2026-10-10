import Mathlib
import OAI.Probability.SLELocalization.TraceModel

namespace OAI


/-! Conformal localization and Is Loewner Trace Using estimates. -/

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.IsLoewnerTraceUsing

lemma positive_solution_live {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {T : ℝ} (hT : 0 ≤ T)
    {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H
      (2/(H t-(driver t:ℂ))) (Icc 0 T) t)
    (hpos : ∀ t ∈ Icc 0 T, 0 < (H t).im) :
    H 0 ∈ localizationDomain γ T ∧ EqOn (fun t => g t (H 0)) H (Icc 0 T) := by
  have hc : ContinuousOn (fun t => (H t).im) (Icc 0 T) :=
    Complex.continuous_im.comp_continuousOn (HasDerivWithinAt.continuousOn hH)
  obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0,le_rfl,hT⟩ hc
  have hpositive := hpos s hs
  let lip : ℝ≥0 := ⟨2 / (H s).im^2, by positivity⟩
  have hlip (time : ℝ) : LipschitzOnWith lip
      (fun point : ℂ => 2 / (point - (driver time : ℂ))) {point | (H s).im ≤ point.im} := by
    have hnorm (point : ℂ) (hpoint : (H s).im ≤ point.im) :
        (H s).im ≤ ‖point - (driver time : ℂ)‖ := by
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
        hpoint.trans (by simpa using Complex.im_le_norm (point - (driver time : ℂ)))
    apply LipschitzOnWith.of_dist_le_mul
    intro left hleft right hright
    have hleftNorm := hnorm left hleft
    have hrightNorm := hnorm right hright
    have hleftNe : left - (driver time : ℂ) ≠ 0 := norm_pos_iff.mp (hpositive.trans_le hleftNorm)
    have hrightNe : right - (driver time : ℂ) ≠ 0 := norm_pos_iff.mp (hpositive.trans_le hrightNorm)
    have hden : (H s).im^2 ≤ ‖(left - (driver time : ℂ)) * (right - (driver time : ℂ))‖ := by
      rw [norm_mul, pow_two]
      exact mul_le_mul hleftNorm hrightNorm hpositive.le (norm_nonneg _)
    have hdiff : 2 / (left - (driver time : ℂ)) - 2 / (right - (driver time : ℂ)) =
        2 * (right - left) / ((left - (driver time : ℂ)) * (right - (driver time : ℂ))) := by
      field_simp
      ring
    simp only [dist_eq_norm, hdiff, norm_div, norm_mul, Complex.norm_ofNat]
    change 2 * ‖right - left‖ / (‖left - (driver time : ℂ)‖ * ‖right - (driver time : ℂ)‖) ≤
      (2 / (H s).im^2) * ‖left - right‖
    calc
      _ ≤ 2 * ‖right - left‖ / (H s).im^2 := by
        apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hpositive)
        simpa only [norm_mul] using hden
      _ = _ := by rw [norm_sub_rev]; ring
  let start := f T (H T)
  have hstart : start ∈ localizationDomain γ T :=
    h.2.2.2.2.2.2.2.2.1 T hT (hpos T ⟨hT, le_rfl⟩)
  have hfinal : g T start = H T :=
    h.2.2.2.2.2.2.2.2.2.2.1 T hT _ (hpos T ⟨hT, le_rfl⟩)
  have hheight (time : ℝ) (htime : time ∈ Icc 0 T) :
      (H s).im ≤ (g time start).im := by
    have hanti := h.height_antitone hT hstart htime ⟨hT, le_rfl⟩ htime.2
    dsimp only at hanti
    rw [hfinal] at hanti
    exact (hmin ⟨hT, le_rfl⟩).trans hanti
  have hder (time : ℝ) (htime : time ∈ Ioc 0 T) :
      HasDerivWithinAt (fun time => g time start)
        (2 / (g time start - (driver time : ℂ))) (Iic time) time := by
    exact (h.hasDerivAt_eval htime.1 (survivingDomain_mono htime.2 hstart)).hasDerivWithinAt
  have heq : EqOn (fun time => g time start) H (Icc 0 T) :=
    ODE_solution_unique_of_mem_Icc_left
      (s := fun _ => {point : ℂ | (H s).im ≤ point.im}) (fun time _ => hlip time)
      (h.continuous_eval hT hstart) hder
      (fun time htime => hheight time ⟨htime.1.le, htime.2⟩)
      (HasDerivWithinAt.continuousOn hH)
      (fun time htime => (hH time ⟨htime.1.le, htime.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem htime))
      (fun _ htime => hmin ⟨htime.1.le, htime.2⟩) hfinal
  have hzero : start = H 0 := by
    rw [← h.initial start hstart.1.1]
    exact heq ⟨le_rfl, hT⟩
  exact ⟨hzero ▸ hstart, hzero ▸ heq⟩

end SLEExactGauge.IsLoewnerTraceUsing

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.BoundaryCutoff

lemma signed_difference_bound {σ : ℝ} (hσ : |σ| = 1) (z w : ℂ) (u v : ℝ) :
    |σ*(z.re-u)-σ*(w.re-v)| ≤ dist z w+|u-v| := by
  rw [← mul_sub,abs_mul,hσ,one_mul]
  calc
    |(z.re-u)-(w.re-v)| = |(z.re-w.re)-(u-v)| := by congr 1; ring
    _ ≤ |z.re-w.re|+|u-v| := abs_sub _ _
    _ ≤ dist z w+|u-v| := by
      have hh := Complex.abs_re_le_norm (z-w)
      simp only [Complex.sub_re] at hh
      rw [dist_eq_norm]
      linarith

lemma neighborhood_live {U : ℝ → ℝ} {H : ℝ → ℂ} {T ε σ : ℝ}
    (hT : 0 < T) (hε : 0 < ε) (hσ : |σ| = 1)
    (_hU : ContinuousOn U (Icc 0 T))
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H
      (2/(H t-(U t:ℂ))) (Icc 0 T) t)
    (hgap : ∀ t ∈ Icc 0 T, ε ≤ σ*((H t).re-U t)) :
    ∃ η : ℝ, 0 < η ∧ ∀ (V : ℝ → ℝ) (ξ : ℝ → ℂ) (G F : ℝ → ℂ → ℂ),
      IsLoewnerTraceUsing V ξ G F → ContinuousOn V (Icc 0 T) →
      (∀ t ∈ Icc 0 T, |V t-U t| < η) →
      ∀ w : ℂ, 0 < w.im → dist w (H 0) < η →
        w ∈ localizationDomain ξ T ∧ ∀ t ∈ Icc 0 T, ε/2 ≤ σ*((G t w).re-V t) := by
  let C := Real.exp ((4/(ε/2)^2)*T)
  have hC : 0 < C := Real.exp_pos _
  let η := ε/(8*(C+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hsmall : 2*η*C+η ≤ ε/2 := by
    have hden : 0 < 8*(C+1) := by positivity
    have he : η*(8*(C+1)) = ε := div_mul_cancel₀ _ hden.ne'
    nlinarith
  have hhalf : 0 < ε/2 := by positivity
  have hbase : ∀ t ∈ Icc 0 T, HasDerivWithinAt H
      (velocity σ (ε/2) (U t) (H t)) (Icc 0 T) t := by
    intro t ht
    rw [velocity_eq hσ (by linarith [hgap t ht])]
    exact hH t ht
  refine ⟨η,hη,fun V ξ G F hξ hV hclose w hw hdist => ?_⟩
  obtain ⟨J,hJ0,hJ⟩ := exists_solution hσ hhalf hT.le V hV w
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : dist (J t) (H t) ≤ 2*η*C := by
    have hh := solution_dist_le hσ hhalf hη.le hη.le hJ hbase
      (by rw [hJ0]; exact hdist.le) (fun t ht => (hclose t ht).le) ht
    simpa only [← two_mul] using hh
  have hg (t : ℝ) (ht : t ∈ Icc 0 T) : ε/2 ≤ σ*((J t).re-V t) := by
    have hh := signed_difference_bound hσ (J t) (H t) (V t) (U t)
    have hn := neg_abs_le (σ*((J t).re-V t)-σ*((H t).re-U t))
    have hs := hgap t ht
    have hcl := hclose t ht
    have hdt := hd t ht
    linarith
  have hder : ∀ t ∈ Icc 0 T, HasDerivWithinAt J
      (2/(J t-(V t:ℂ))) (Icc 0 T) t := by
    intro t ht
    have hh := hJ t ht
    rw [velocity_eq hσ (hg t ht)] at hh
    exact hh
  have hpos := positive_height hσ hhalf hJ (by rw [hJ0]; exact hw)
  have hl := hξ.positive_solution_live hT.le hder hpos
  rw [hJ0] at hl
  refine ⟨hl.1,fun t ht => ?_⟩
  have he : G t w = J t := hl.2 ht
  rw [he]
  exact hg t ht

end SLEExactGauge.BoundaryCutoff

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge

theorem separated_forward_path_avoids_trace
    {U : ℝ → ℝ} {H : ℝ → ℂ} {T ε σ : ℝ}
    (hT : 0 < T) (hε : 0 < ε) (hσ : |σ| = 1)
    (hU : ContinuousOn U (Icc 0 T))
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H
      (2/(H t-(U t:ℂ))) (Icc 0 T) t)
    (hgap : ∀ t ∈ Icc 0 T, ε ≤ σ*((H t).re-U t)) :
    ∃ η : ℝ, 0 < η ∧ ∀ (V : ℝ → ℝ) (ξ : ℝ → ℂ) (G F : ℝ → ℂ → ℂ),
      IsLoewnerTraceUsing V ξ G F → ContinuousOn V (Icc 0 T) →
      (∀ t ∈ Icc 0 T, |V t-U t| < η) →
      ∀ t ∈ Icc 0 T, η ≤ dist (ξ t) (H 0) := by
  obtain ⟨η,hη,hlive⟩ := BoundaryCutoff.neighborhood_live hT hε hσ hU hH hgap
  refine ⟨η,hη,fun V ξ G F hξ hV hclose t ht => ?_⟩
  by_contra hn
  have hlt : dist (ξ t) (H 0) < η := lt_of_not_ge hn
  have htip := hξ.2.2.2.2.2.2.2.2.2.2.2.2.2 t ht.1
  have he : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), dist (F t ((V t:ℂ)+(y:ℂ)*Complex.I)) (H 0) < η :=
    htip.eventually (isOpen_ball.mem_nhds (show ξ t ∈ ball (H 0) η from hlt))
  have hp : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), 0 < y := self_mem_nhdsWithin
  obtain ⟨y,hy,hball⟩ := (hp.and he).exists
  have hz : (V t:ℂ)+(y:ℂ)*Complex.I ∈ halfPlane := by
    change 0 < ((V t:ℂ)+(y:ℂ)*Complex.I).im
    simpa using hy
  have hfw := hξ.2.2.2.2.2.2.2.2.1 t ht.1 hz
  have hl := hlive V ξ G F hξ hV hclose _ hfw.1.1 hball
  have hg := hl.2 t ht
  rw [hξ.2.2.2.2.2.2.2.2.2.2.1 t ht.1 _ hz] at hg
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,add_zero,sub_self] at hg
  linarith

end SLEExactGauge

end

end

end OAI

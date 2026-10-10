import Mathlib
import OAI.Probability.SLE.BrownianStrongMarkov

namespace OAI

/-! Disk Half Plane for chordal SLE. -/

section
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def diskToHalfPlane (w ζ : ℂ) : ℂ := (w - star w * ζ) / (1 - ζ)

lemma disk_denominator_ne {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) : 1 - ζ ≠ 0 := by
  intro he
  have hh := mem_ball_zero_iff.mp hζ
  rw [← sub_eq_zero.mp he] at hh
  simp at hh

lemma diskToHalfPlane_im (w ζ : ℂ) :
    (diskToHalfPlane w ζ).im = w.im * (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := by
  simp only [diskToHalfPlane, Complex.div_im, Complex.sub_im, Complex.sub_re, Complex.mul_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.one_im,
    Complex.one_re, Complex.normSq_apply]
  ring

lemma diskToHalfPlane_maps {w : ℂ} (hw : 0 < w.im) :
    MapsTo (diskToHalfPlane w) (ball 0 1) upperHalfPlane := by
  intro ζ hζ
  have hn : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hn2 : Complex.normSq ζ < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
  have hp : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.mpr (disk_denominator_ne hζ)
  change 0 < (diskToHalfPlane w ζ).im
  rw [diskToHalfPlane_im]
  exact div_pos (mul_pos hw (sub_pos.mpr hn2)) hp

lemma diskToHalfPlane_differentiable (w : ℂ) :
    DifferentiableOn ℂ (diskToHalfPlane w) (ball 0 1) :=
  ((differentiableOn_id.const_mul (star w)).const_sub w).div
    (differentiableOn_id.const_sub 1) (fun _ hζ => disk_denominator_ne hζ)

@[simp] lemma diskToHalfPlane_zero (w : ℂ) : diskToHalfPlane w 0 = w := by simp [diskToHalfPlane]

lemma diskToHalfPlane_deriv_zero (w : ℂ) :
    HasDerivAt (diskToHalfPlane w) (w - star w) 0 := by
  have hh := ((hasDerivAt_const (0 : ℂ) w).sub ((hasDerivAt_id 0).const_mul (star w))).div
    ((hasDerivAt_const (0 : ℂ) 1).sub (hasDerivAt_id 0)) (by norm_num : (1 : ℂ) - 0 ≠ 0)
  convert hh using 1 <;> first | rfl | (dsimp; ring)

lemma diskToHalfPlane_injOn {w : ℂ} (hw : 0 < w.im) : InjOn (diskToHalfPlane w) (ball 0 1) := by
  intro ζ hζ ξ hξ he
  have hc := (div_eq_div_iff (disk_denominator_ne hζ) (disk_denominator_ne hξ)).mp he
  have hp : (w - star w) * (ζ - ξ) = 0 := by linear_combination hc
  have hn : w - star w ≠ 0 := by
    intro he
    have him := congrArg Complex.im he
    simp at him
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hn)

lemma norm_sub_conj_of_im_pos {w : ℂ} (hw : 0 < w.im) : ‖w - star w‖ = 2 * w.im := by
  rw [Complex.star_def, Complex.sub_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) hw), Complex.norm_I, mul_one]

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.radius_le_omitted_distance
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (_hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (a : ℂ) (ha : a ∉ survivingDomain γ t) :
    fullRadius G t z ≤ (128 * Real.pi) * dist z a := by
  have hγ := h.1
  rcases h with ⟨_, hγ0, hγim, hG, hF, hGmap, hFmap, hinv, hinv', h0, hode, hnorm, htip⟩
  have hy : 0 < (G t z).im := hGmap t hz
  have hg := ((hG t).differentiableAt ((isOpen_survivingDomain hγ t).mem_nhds hz)).hasDerivAt
  have hf := ((hF t).differentiableAt (isOpen_upperHalfPlane.mem_nhds (hGmap t hz))).hasDerivAt
  have hident : (fun v => F t (G t v)) =ᶠ[𝓝 z] (fun v => v) := by
    filter_upwards [(isOpen_survivingDomain hγ t).mem_nhds hz] with v hv
    exact hinv t v hv
  have hprod : deriv (F t) (G t z) * deriv (G t) z = 1 :=
    ((hf.comp z hg).congr_of_eventuallyEq hident.symm).unique (hasDerivAt_id z)
  have hnormprod : ‖deriv (F t) (G t z)‖ * ‖deriv (G t) z‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hgpos : 0 < ‖deriv (G t) z‖ := by
    by_contra hn
    have he : ‖deriv (G t) z‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [he, mul_zero] at hnormprod
    norm_num at hnormprod
  let f : ℂ → ℂ := F t ∘ diskToHalfPlane (G t z)
  have hfd : DifferentiableOn ℂ f (ball 0 1) :=
    (hF t).comp (diskToHalfPlane_differentiable _) (diskToHalfPlane_maps hy)
  have hfi : InjOn f (ball 0 1) := by
    intro v hv w hw he
    apply diskToHalfPlane_injOn hy hv hw
    have he' := congrArg (G t) he
    change G t (F t (diskToHalfPlane (G t z) v)) = G t (F t (diskToHalfPlane (G t z) w)) at he'
    rwa [hinv' t _ (diskToHalfPlane_maps hy hv), hinv' t _ (diskToHalfPlane_maps hy hw)] at he'
  have hfimage : f '' ball 0 1 ⊆ survivingDomain γ t := by
    rintro _ ⟨v, hv, rfl⟩
    exact hFmap t (diskToHalfPlane_maps hy hv)
  have hfv0 : f 0 = z := by simp only [f, Function.comp_apply, diskToHalfPlane_zero, hinv t z hz]
  have hfq : HasDerivAt (F t) (deriv (F t) (G t z)) (diskToHalfPlane (G t z) 0) := by simpa using hf
  have hfder : deriv f 0 = deriv (F t) (G t z) * (G t z - star (G t z)) :=
    (hfq.comp 0 (diskToHalfPlane_deriv_zero _)).deriv
  have hfrad : ‖deriv f 0‖ = fullRadius G t z := by
    rw [hfder, norm_mul, norm_sub_conj_of_im_pos hy, fullRadius]
    apply (eq_div_iff hgpos.ne').mpr
    nlinarith [hnormprod]
  have hh := univalent_omitted_value_bound hfd hfi a (fun ha' => ha (hfimage ha'))
  rwa [hfrad, hfv0, ← dist_eq_norm] at hh

lemma IsCapacityTwoWitness.radius_le_past_distance
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (s : ℝ≥0) (hs : s ≤ t) :
    fullRadius G t z ≤ (128 * Real.pi) * dist z (γ s) :=
  h.radius_le_omitted_distance hU t z hz (γ s)
    (fun hw => hw.1.2 ⟨s, ⟨zero_le, hs⟩, rfl⟩)

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.radius_approach_of_trace_approach
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (T : ℝ≥0) (hT : dist (γ T) z < r) :
    ∃ s : ℝ≥0, s ≤ T ∧ z ∈ survivingDomain γ s ∧ fullRadius G s z < (128 * Real.pi) * r := by
  let ρ : ℝ := (r + dist (γ T) z) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith [(dist_nonneg : 0 ≤ dist (γ T) z)]
  have hρr : ρ < r := by dsimp [ρ]; linarith
  have hTρ : dist (γ T) z < ρ := by dsimp [ρ]; linarith
  have hγ : Continuous γ := h.1
  let S : Set ℝ≥0 := Icc 0 T ∩ {s | dist (γ s) z ≤ ρ}
  have hSc : IsCompact S := isCompact_Icc.inter_right (isClosed_le (hγ.dist continuous_const) continuous_const)
  have hSn : S.Nonempty := ⟨T, ⟨⟨zero_le, le_rfl⟩, hTρ.le⟩⟩
  obtain ⟨τ, hτ, hmin⟩ := hSc.exists_isMinOn hSn continuous_id.continuousOn
  have hτ0 : 0 < τ := by
    by_contra hn
    have he : τ = 0 := le_antisymm (le_of_not_gt hn) zero_le
    have hh := hτ.2
    change dist (γ τ) z ≤ ρ at hh
    rw [he, h.2.1, dist_zero_left] at hh
    have hz := Complex.im_le_norm z
    linarith
  have hprior (s : ℝ≥0) (hs : s < τ) : ρ < dist (γ s) z := by
    by_contra hn
    have hmem : s ∈ S := ⟨⟨zero_le, hs.le.trans hτ.1.2⟩, le_of_not_gt hn⟩
    exact not_le_of_gt hs (hmin hmem)
  have hτcl : τ ∈ closure (Ioo (0 : ℝ≥0) τ) := by
    rw [closure_Ioo (ne_of_lt hτ0)]
    exact ⟨hτ0.le, le_rfl⟩
  have hO : IsOpen {s : ℝ≥0 | dist (γ s) z < r} := isOpen_lt (hγ.dist continuous_const) continuous_const
  have hτO : τ ∈ {s : ℝ≥0 | dist (γ s) z < r} := lt_of_le_of_lt hτ.2 hρr
  obtain ⟨s, hsnear, hs⟩ := mem_closure_iff.mp hτcl _ hO hτO
  have hsT : s ≤ T := hs.2.le.trans hτ.1.2
  have hfree : ball z ρ ⊆ upperHalfPlane \ (γ '' Icc 0 s) := by
    intro w hw
    refine ⟨ball_subset_upperHalfPlane (hρr.le.trans hy) hw, ?_⟩
    rintro ⟨u, hu, rfl⟩
    exact not_lt_of_ge (hprior u (hu.2.trans_lt hs.2)).le (mem_ball.mp hw)
  have hsz := h.surviving_of_free_ball_future_tip s T hsT z ρ hρ hfree (mem_ball.mpr hTρ)
  refine ⟨s, hsT, hsz, ?_⟩
  have hh := h.radius_le_past_distance hU s z hsz s le_rfl
  rw [dist_comm z (γ s)] at hh
  exact hh.trans_lt (mul_lt_mul_of_pos_left hsnear (mul_pos (by norm_num) Real.pi_pos))

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma logRadiusClock_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t) :
    logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) =
      Real.log ((2 * z.im) / fullRadius G t z) := by
  have hy := h.imag_positive t z hz
  have hj := h.derivative_norm_positive hU t z hz
  have hR := h.fullRadius_positive hU t z hz
  rw [logRadiusClock, logCoordinates_im, logCoordinates_snd,
    Real.log_div (mul_ne_zero (by norm_num) hz.1.1.ne') hR.ne',
    Real.log_mul (by norm_num) hz.1.1.ne', fullRadius,
    Real.log_div (mul_ne_zero (by norm_num) hy.ne') hj.ne',
    Real.log_mul (by norm_num) hy.ne']
  ring

lemma fullRadius_eq_logClock
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t) :
    fullRadius G t z = (2 * z.im) *
      Real.exp (-logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t)) := by
  rw [logRadiusClock_logCoordinates hU h z t hz, Real.exp_neg,
    Real.exp_log (div_pos (mul_pos (by norm_num) hz.1.1) (h.fullRadius_positive hU t z hz))]
  field_simp [(show 0 < z.im from hz.1.1).ne']

lemma fullRadius_level_iff_logClock
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t) (u : ℝ) :
    fullRadius G t z = (2 * z.im) * Real.exp (-u) ↔
      logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) = u := by
  rw [fullRadius_eq_logClock hU h z t hz,
    mul_right_inj' (mul_ne_zero (by norm_num) hz.1.1.ne'), Real.exp_eq_exp, neg_inj]

lemma IsCapacityTwoWitness.radius_clock_strictMonoOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (T : ℝ≥0) (hz : z ∈ survivingDomain γ T) :
    StrictMonoOn (fun t : ℝ => Real.log ((2 * z.im) / fullRadius G t.toNNReal z))
      (Icc 0 (T : ℝ)) := by
  have hd := loewner_radius_clock_derivative hU h T z hz
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
  intro t ht
  have hy := h.imag_positive t.toNNReal z (h.live_at_real_time T z hz t (interior_subset ht).2)
  have hn := Complex.normSq_pos.mpr (h.centered_ne_zero t.toNNReal z
    (h.live_at_real_time T z hz t (interior_subset ht).2))
  positivity

lemma live_radius_unique
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (s t : ℝ≥0) (hs : z ∈ survivingDomain γ s)
    (ht : z ∈ survivingDomain γ t) (he : fullRadius G s z = fullRadius G t z) : s = t := by
  have hmax : z ∈ survivingDomain γ (max s t) := by
    rcases le_total s t with hh | hh
    · simpa only [max_eq_right hh] using ht
    · simpa only [max_eq_left hh] using hs
  have hi := h.radius_clock_strictMonoOn hU z (max s t) hmax
  apply NNReal.coe_injective
  apply hi.injOn
  · exact ⟨s.coe_nonneg, by exact_mod_cast le_max_left s t⟩
  · exact ⟨t.coe_nonneg, by exact_mod_cast le_max_right s t⟩
  · simp only [Real.toNNReal_coe, he]

lemma live_clock_le_time
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (s t : ℝ≥0) (hs : z ∈ survivingDomain γ s)
    (_ht : z ∈ survivingDomain γ t)
    (he : Real.log ((2 * z.im) / fullRadius G s z) ≤
      Real.log ((2 * z.im) / fullRadius G t z)) : s ≤ t := by
  by_contra hn
  have hts := not_le.mp hn
  have hi := h.radius_clock_strictMonoOn hU z s hs
  have hh := hi (show (t : ℝ) ∈ Icc 0 (s : ℝ) from ⟨t.coe_nonneg, by exact_mod_cast hts.le⟩)
    (show (s : ℝ) ∈ Icc 0 (s : ℝ) from ⟨s.coe_nonneg, le_rfl⟩) (by exact_mod_cast hts)
  simp only [Real.toNNReal_coe] at hh
  exact (not_lt_of_ge he) hh

lemma live_angleSq_lower_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (T : ℝ≥0) (hz : z ∈ survivingDomain γ T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, t ≤ T →
      δ ≤ (Real.sin (Complex.arg (G t z - (U t : ℂ)))) ^ 2 := by
  let A (t : ℝ) := (Real.sin (Complex.arg (G t.toNNReal z - (U t.toNNReal : ℂ)))) ^ 2
  have hn (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
      ‖G t.toNNReal z - (U t.toNNReal : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (h.centered_ne_zero _ z (h.live_at_real_time T z hz t ht.2))
  have hc : ContinuousOn A (Icc 0 (T : ℝ)) := by
    have hGc := h.time_continuousOn T z hz
    have hUc := Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)
    have hZc := hGc.sub hUc.continuousOn
    simp only [A, Complex.sin_arg]
    exact ((Complex.continuous_im.comp_continuousOn hZc).div hZc.norm hn).pow 2
  obtain ⟨t, ht, hmin⟩ := (isCompact_Icc : IsCompact (Icc 0 (T : ℝ))).exists_isMinOn
    ⟨0, le_rfl, T.coe_nonneg⟩ hc
  have hp : 0 < A t := by
    have hy := h.imag_positive t.toNNReal z (h.live_at_real_time T z hz t ht.2)
    dsimp only [A]
    rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact sq_pos_of_pos (div_pos hy (lt_of_le_of_ne (norm_nonneg _) (hn t ht).symm))
  refine ⟨A t, hp, fun s hs => ?_⟩
  have hh := hmin (show (s : ℝ) ∈ Icc 0 (T : ℝ) from ⟨s.coe_nonneg, by exact_mod_cast hs⟩)
  change A t ≤ A (s : ℝ) at hh
  simpa only [A, Real.toNNReal_coe] using hh

lemma radiusLevelTime_eq_of_live_level
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (t : ℝ≥0) (ht : z ∈ survivingDomain γ t)
    (hR : fullRadius G t z = (2 * z.im) * Real.exp (-u)) :
    radiusLevelTime γ G z u = (t : ℝ≥0∞) := by
  have he : {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
      fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)} = {(t : ℝ≥0∞)} := by
    ext s
    constructor
    · rintro ⟨hs, hsl, hsR⟩
      have hh : s.toNNReal = t := live_radius_unique hU h z s.toNNReal t hsl ht (hsR.trans hR.symm)
      have hse : (s.toNNReal : ℝ≥0∞) = s := ENNReal.coe_toNNReal hs.ne
      rw [Set.mem_singleton_iff, ← hse, hh]
    · intro hs
      rw [Set.mem_singleton_iff] at hs
      subst s
      simpa only [Set.mem_ofPred_eq, ENNReal.coe_lt_top, ENNReal.toNNReal_coe, true_and] using And.intro ht hR
  rw [radiusLevelTime, he, sInf_singleton]

lemma stoppedGreen_eq_of_live_level
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (κ : ℝ) (z : ℂ) (u : ℝ) (t : ℝ≥0) (ht : z ∈ survivingDomain γ t)
    (hR : fullRadius G t z = (2 * z.im) * Real.exp (-u)) :
    stoppedGreen κ U γ G z u = greenDensity κ U γ G t z := by
  rw [stoppedGreen, radiusLevelTime_eq_of_live_level hU h z u t ht hR]
  simp only [ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe]

lemma stoppedGreen_eq_zero_of_no_level
    (κ : ℝ) (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ)
    (hn : ¬ ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧
      fullRadius G t z = (2 * z.im) * Real.exp (-u)) :
    stoppedGreen κ U γ G z u = 0 := by
  have he : {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
      fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨_, hsl, hsR⟩
    exact hn ⟨s.toNNReal, hsl, hsR⟩
  simp only [stoppedGreen, radiusLevelTime, he, sInf_empty, lt_self_iff_false, ↓reduceIte]

end SLEExactGauge
end

 
section

open Set Filter
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsCapacityTwoWitness.fullRadius_initial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (hz : z ∈ survivingDomain γ 0) :
    fullRadius G 0 z = 2 * z.im := by
  rw [fullRadius, h.initial_value z hz.1.1,
    loewner_spatial_derivative hU h 0 z hz]
  simp

 

lemma radiusLevelTime_finite_of_live_radius_lt
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0)
    (ht : z ∈ survivingDomain γ t)
    (hR : fullRadius G t z < (2 * z.im) * Real.exp (-u)) :
    radiusLevelTime γ G z u < ∞ := by
  let L : ℝ → ℝ := fun s => Real.log ((2 * z.im) / fullRadius G s.toNNReal z)
  have hy : 0 < 2 * z.im := mul_pos (by norm_num) ht.1.1
  have hz0 : z ∈ survivingDomain γ 0 := survivingDomain_antitone γ zero_le ht
  have hL0 : L 0 = 0 := by
    simp only [L, Real.toNNReal_zero, h.fullRadius_initial hU z hz0,
      div_self hy.ne', Real.log_one]
  have hLt : u < L t := by
    have he := fullRadius_eq_logClock hU h z t ht
    rw [he] at hR
    have hc := (mul_lt_mul_iff_right₀ hy).mp hR
    rw [Real.exp_lt_exp] at hc
    dsimp only [L]
    rw [Real.toNNReal_coe, ← logRadiusClock_logCoordinates hU h z t ht]
    linarith
  have hLc : ContinuousOn L (Icc 0 (t : ℝ)) :=
    fun s hs => (loewner_radius_clock_derivative hU h t z ht s hs).continuousWithinAt
  obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc t.coe_nonneg hLc
    (show u ∈ Icc (L 0) (L t) from ⟨by rwa [hL0], hLt.le⟩)
  have hsl : z ∈ survivingDomain γ s.toNNReal := h.live_at_real_time t z ht s hs.2
  have hsr : fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u) := by
    apply (fullRadius_level_iff_logClock hU h z s.toNNReal hsl u).mpr
    rw [logRadiusClock_logCoordinates hU h z s.toNNReal hsl]
    exact hsu
  rw [radiusLevelTime_eq_of_live_level hU h z u s.toNNReal hsl hsr]
  exact ENNReal.coe_lt_top

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure FiniteIncreasingClock (Ω : Type*) where
  S : ℝ → Ω → ℝ
  T : Ω → ℝ≥0
  zero : ∀ ω, S 0 ω = 0
  continuous : ∀ ω, Continuous (fun t => S t ω)
  strict : ∀ ω, StrictMonoOn (fun t => S t ω) (Icc 0 (T ω : ℝ))

namespace FiniteIncreasingClock
variable {Ω : Type*} (c : FiniteIncreasingClock Ω)

lemma terminal_nonneg (ω : Ω) : 0 ≤ c.S (c.T ω) ω := by
  rw [← c.zero ω]
  exact (c.strict ω).monotoneOn ⟨le_rfl, (c.T ω).coe_nonneg⟩
    ⟨(c.T ω).coe_nonneg, le_rfl⟩ (c.T ω).coe_nonneg

noncomputable def iso (ω : Ω) : Icc (0 : ℝ) (c.T ω : ℝ) ≃o Icc (0 : ℝ) (c.S (c.T ω) ω) := by
  let f : Icc (0 : ℝ) (c.T ω : ℝ) → Icc (0 : ℝ) (c.S (c.T ω) ω) := fun t =>
    ⟨c.S t ω, by
      constructor
      · simpa only [c.zero ω] using
          ((c.strict ω).monotoneOn ⟨le_rfl, (c.T ω).coe_nonneg⟩ t.property t.property.1)
      · exact (c.strict ω).monotoneOn t.property ⟨(c.T ω).coe_nonneg, le_rfl⟩ t.property.2⟩
  apply StrictMono.orderIsoOfSurjective f
  · intro s t hst
    exact c.strict ω s.property t.property hst
  · intro s
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc (c.T ω).coe_nonneg
      (c.continuous ω).continuousOn (show (s : ℝ) ∈ Icc (c.S 0 ω) (c.S (c.T ω) ω) by
        simpa only [c.zero ω] using s.property)
    exact ⟨⟨t, ht⟩, Subtype.ext he⟩

lemma iso_apply (ω : Ω) (t : Icc (0 : ℝ) (c.T ω : ℝ)) :
    (c.iso ω t : ℝ) = c.S t ω := rfl

noncomputable def inverse (s : ℝ) (ω : Ω) : ℝ :=
  ((c.iso ω).symm ⟨min (max s 0) (c.S (c.T ω) ω),
    ⟨le_min (le_max_right _ _) (c.terminal_nonneg ω), min_le_right _ _⟩⟩ : ℝ)

lemma inverse_mem (s : ℝ) (ω : Ω) : c.inverse s ω ∈ Icc (0 : ℝ) (c.T ω : ℝ) :=
  ((c.iso ω).symm _).property

lemma clock_inverse (s : ℝ) (ω : Ω) :
    c.S (c.inverse s ω) ω = min (max s 0) (c.S (c.T ω) ω) := by
  exact congrArg Subtype.val ((c.iso ω).apply_symm_apply _)

lemma inverse_clock (ω : Ω) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (c.T ω : ℝ)) :
    c.inverse (c.S t ω) ω = t := by
  apply (c.strict ω).injOn (c.inverse_mem _ ω) ht
  dsimp only
  rw [c.clock_inverse]
  have h0 : 0 ≤ c.S t ω := by
    rw [← c.zero ω]
    exact (c.strict ω).monotoneOn ⟨le_rfl, (c.T ω).coe_nonneg⟩ ht ht.1
  have hT := (c.strict ω).monotoneOn ht ⟨(c.T ω).coe_nonneg, le_rfl⟩ ht.2
  rw [max_eq_left h0, min_eq_left hT]

lemma continuous_inverse (ω : Ω) : Continuous (fun s => c.inverse s ω) := by
  apply continuous_subtype_val.comp
  apply (c.iso ω).symm.continuous.comp
  exact Continuous.subtype_mk ((continuous_id.max continuous_const).min continuous_const) _

lemma inverse_le_iff (s : ℝ) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
    c.inverse s ω ≤ t ↔ (c.T ω : ℝ) ≤ t ∨
      min (max s 0) (c.S (c.T ω) ω) ≤ c.S t ω := by
  by_cases hT : (c.T ω : ℝ) ≤ t
  · exact iff_of_true ((c.inverse_mem s ω).2.trans hT) (Or.inl hT)
  · have htm : t ∈ Icc (0 : ℝ) (c.T ω : ℝ) := ⟨ht, (lt_of_not_ge hT).le⟩
    rw [or_iff_right hT, ← c.clock_inverse]
    exact ((c.strict ω).le_iff_le (c.inverse_mem s ω) htm).symm

lemma measurable_inverse [MeasurableSpace Ω]
    (hS : Measurable (Function.uncurry c.S)) (hT : Measurable c.T) :
    Measurable (Function.uncurry c.inverse) := by
  apply measurable_of_Iic
  intro t
  by_cases ht : 0 ≤ t
  · have hterminal : Measurable (fun ω => c.S (c.T ω) ω) :=
      hS.comp ((measurable_coe_nnreal_real.comp hT).prodMk measurable_id)
    have he : (Function.uncurry c.inverse) ⁻¹' Iic t =
        {p : ℝ × Ω | (c.T p.2 : ℝ) ≤ t} ∪
        {p : ℝ × Ω | min (max p.1 0) (c.S (c.T p.2) p.2) ≤ c.S t p.2} := by
      ext p
      exact c.inverse_le_iff p.1 p.2 t ht
    rw [he]
    exact (measurableSet_le ((measurable_coe_nnreal_real.comp hT).comp measurable_snd) measurable_const).union
      (measurableSet_le ((measurable_fst.max measurable_const).min (hterminal.comp measurable_snd))
        (hS.comp (measurable_const.prodMk measurable_snd)))
  · have he : (Function.uncurry c.inverse) ⁻¹' Iic t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact ht ((c.inverse_mem p.1 p.2).1.trans hp)
    rw [he]
    exact MeasurableSet.empty

end FiniteIncreasingClock
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma powerLogDensity_pos (κ p α : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0 < powerLogDensity κ p α q x := Real.exp_pos _

lemma powerLogDensity_le_radius
    (κ p α η₀ u : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ α) (q : ℂ × ℝ) (x : ℝ)
    (hs : logRadiusClock η₀ q ≤ u) :
    powerLogDensity κ p α q x ≤ Real.exp (p * (u - Real.log 2 - η₀)) := by
  rw [powerLogDensity_radius_angle κ p α η₀ q x]
  have ha' : (logAngleSq κ q x) ^ (α / 2) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (logAngleSq_pos κ q x).le
      (logAngleSq_le_one κ q x) (div_nonneg ha (by norm_num))
  calc
    _ ≤ Real.exp (p * (logRadiusClock η₀ q - Real.log 2 - η₀)) * 1 :=
      mul_le_mul_of_nonneg_left ha' (Real.exp_pos _).le
    _ ≤ _ := by rw [mul_one]; apply Real.exp_le_exp.mpr; gcongr

lemma powerLogGenerator_abs_bound
    (κ p α lo : ℝ) (q : ℂ × ℝ) (x : ℝ) (hlo : lo ≤ q.1.im) :
    |powerLogGenerator κ p α q x| ≤
      powerLogDensity κ p α q x *
        (|(-4 * α + κ * α * (α + 1) / 2)| + |(4 * p - κ * α / 2)|) /
          Real.exp (2 * lo) := by
  let A := -4 * α + κ * α * (α + 1) / 2
  let D := 4 * p - κ * α / 2
  let X := q.1.re - Real.sqrt κ * x
  let Y := Real.exp (2 * q.1.im)
  let N := greenLogNormSq κ q x
  let φ := powerLogDensity κ p α q x
  have hN : 0 < N := greenLogNormSq_pos κ q x
  have hY : 0 < Y := Real.exp_pos _
  have hφ : 0 ≤ φ := (powerLogDensity_pos κ p α q x).le
  have hX : X ^ 2 ≤ N := le_add_of_nonneg_right hY.le
  have hYN : Y ≤ N := le_add_of_nonneg_left (sq_nonneg _)
  have hlow : Real.exp (2 * lo) ≤ N :=
    (Real.exp_le_exp.mpr (by linarith)).trans hYN
  have hnum : |A * X ^ 2 + D * Y| ≤ (|A| + |D|) * N := by
    calc
      _ ≤ |A * X ^ 2| + |D * Y| := abs_add_le _ _
      _ = |A| * X ^ 2 + |D| * Y := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg X), abs_of_pos hY]
      _ ≤ |A| * N + |D| * N := add_le_add
        (mul_le_mul_of_nonneg_left hX (abs_nonneg A))
        (mul_le_mul_of_nonneg_left hYN (abs_nonneg D))
      _ = _ := by ring
  change |φ * (A * X ^ 2 + D * Y) / N ^ 2| ≤ φ * (|A| + |D|) / _
  rw [abs_div, abs_mul, abs_of_nonneg hφ, abs_of_nonneg (sq_nonneg N)]
  calc
    _ ≤ φ * ((|A| + |D|) * N) / N ^ 2 := by gcongr
    _ = φ * (|A| + |D|) / N := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hlow

lemma powerLogGenerator_le_radius_height
    (κ p α η₀ u lo : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ α) (q : ℂ × ℝ) (x : ℝ)
    (hs : logRadiusClock η₀ q ≤ u) (hlo : lo ≤ q.1.im) :
    |powerLogGenerator κ p α q x| ≤
      Real.exp (p * (u - Real.log 2 - η₀)) *
        (|(-4 * α + κ * α * (α + 1) / 2)| + |(4 * p - κ * α / 2)|) /
          Real.exp (2 * lo) := by
  apply (powerLogGenerator_abs_bound κ p α lo q x hlo).trans
  apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (powerLogDensity_le_radius κ p α η₀ u hp ha q x hs)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem exists_finite_angular_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ logAngleSq κ (initialLogCoordinates z) 0) :
    ∃ f : Ω → ℝ,
      Integrable f P ∧ (∫ ω, f ω ∂P) = initialGreen κ z ∧
      (∀ ω, 0 ≤ f ω ∧ f ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))) ∧
      ∀ (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
        IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F →
        ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧
          Real.log ((2 * z.im) / fullRadius G t z) ≤ u ∧
          (Real.log ((2 * z.im) / fullRadius G t z) = u ∨
            (Real.sin (Complex.arg (G t z - ((Real.sqrt κ * B t ω : ℝ) : ℂ)))) ^ 2 = ε) ∧
          f ω = greenDensity κ (fun t => Real.sqrt κ * B t ω) γ G t z ∧
          ((Real.sin (Complex.arg (G t z - ((Real.sqrt κ * B t ω : ℝ) : ℂ)))) ^ 2 = ε →
            f ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) *
              ε ^ (greenExponent κ / 2)) := by
  let η₀ := Real.log z.im
  let lo := η₀ - u / (2 * ε) - 1
  let hi := η₀ + 1
  have hule : 0 ≤ u / (2 * ε) := by positivity
  have hle : lo ≤ hi := by dsimp [lo, hi]; linarith
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨c⟩ := exists_clippedLogSolution B hm hBm hBc κ lo hi hle (initialLogCoordinates z)
  have hη : (initialLogCoordinates z).1.im = η₀ := by
    simp only [initialLogCoordinates, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
    rfl
  let a := 4 * ε ^ 2 / Real.exp (2 * η₀)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (u / a)
  have hT : u < (4 * ε ^ 2 / Real.exp (2 * (initialLogCoordinates z).1.im)) * ((N : ℝ≥0) : ℝ) := by
    rw [hη]
    have hh := (div_lt_iff₀ ha).mp hN
    simpa only [NNReal.coe_natCast, mul_comm (N : ℝ) a] using hh
  obtain ⟨τ, hτ, ht, hin, hpre, hbound, hfi, hfm⟩ := c.finite_angular_law
    hB hBm hBc hB0 hκ hκ8 rfl u ε hu hε hε0
    (by rw [hη]; dsimp [lo]; linarith) (by rw [hη]; dsimp [hi]; linarith) (N : ℝ≥0) hT
  let f (ω : Ω) := greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)
  refine ⟨f, hfi, hfm.trans (greenLogDensity_initial κ z hz), ?_, ?_⟩
  · intro ω
    refine ⟨greenLogDensity_nonneg _ _ _, ?_⟩
    have hh := greenLogDensity_le_radius κ (initialLogCoordinates z).1.im u hκ hκ8 (c.Q (τ ω) ω) (B (τ ω) ω)
      (hin ω (τ ω) le_rfl).1
    simpa only [hη] using hh
  · intro ω γ G F hw
    have hU : Continuous (fun t => Real.sqrt κ * B t ω) := (hBc ω).const_mul _
    have hQd (s : ℝ) (hs : s ∈ Icc 0 (τ ω : ℝ)) := (c.derivative ω s hs.1).mono
      (show Icc (0 : ℝ) (τ ω : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
    have hQb (s : ℝ) (hs : s ∈ Icc 0 (τ ω : ℝ)) : (c.Q s ω).1.im ∈ Icc lo hi := by
      have hh := (hin ω s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)).2.2
      simpa only [Set.mem_Icc, Real.coe_toNNReal _ hs.1] using hh
    obtain ⟨hlive, heq⟩ := clipped_log_identification hU hw z hz (τ ω) lo hi hle
      (fun s => c.Q s ω) (c.initial ω) hQd hQb
    have he : c.Q (τ ω) ω = logLoewnerCoordinates G z (τ ω) :=
      heq ⟨(τ ω).coe_nonneg, le_rfl⟩
    have hr : logRadiusClock (initialLogCoordinates z).1.im (c.Q (τ ω) ω) =
        Real.log ((2 * z.im) / fullRadius G (τ ω) z) := by
      rw [he, hη]
      exact logRadiusClock_logCoordinates hU hw z (τ ω) hlive
    have ha' : logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) =
        (Real.sin (Complex.arg (G (τ ω) z - ((Real.sqrt κ * B (τ ω) ω : ℝ) : ℂ)))) ^ 2 := by
      rw [he]
      exact logAngleSq_logCoordinates κ _ G z _ (hw.imag_positive _ z hlive)
    refine ⟨τ ω, hlive, ?_, ?_, ?_, ?_⟩
    · simpa only [hr] using (hin ω (τ ω) le_rfl).1
    · simpa only [hr, ha'] using hbound ω
    · dsimp only [f]
      rw [he]
      exact greenLogDensity_logCoordinates hU hw κ _ z _ hlive rfl
    · intro hA
      have hh := greenLogDensity_le_at_angular_exit κ (initialLogCoordinates z).1.im u ε hκ hκ8
        (c.Q (τ ω) ω) (B (τ ω) ω) (hin ω (τ ω) le_rfl).1 (by rw [ha', hA])
      simpa only [hη] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure AngularLocalization {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t)) (κ : ℝ)
    (z : ℂ) (u ε : ℝ) where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi
  solution : ClippedLogSolution B hm κ lo hi le (initialLogCoordinates z)
  T : ℝ≥0
  τ : Ω → ℝ≥0
  stopping : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω : WithTop ℝ≥0))
  bounded : ∀ ω, τ ω ≤ T
  inside : ∀ ω t, t ≤ τ ω →
    logRadiusClock (Real.log z.im) (solution.Q t ω) ≤ u ∧
    ε ≤ logAngleSq κ (solution.Q t ω) (B t ω) ∧
    lo ≤ (solution.Q t ω).1.im ∧ (solution.Q t ω).1.im ≤ hi
  before : ∀ ω t, t < τ ω →
    logRadiusClock (Real.log z.im) (solution.Q t ω) < u ∧
    ε < logAngleSq κ (solution.Q t ω) (B t ω)
  boundary : ∀ ω,
    logRadiusClock (Real.log z.im) (solution.Q (τ ω) ω) = u ∨
    logAngleSq κ (solution.Q (τ ω) ω) (B (τ ω) ω) = ε

lemma initialLogCoordinates_im (z : ℂ) :
    (initialLogCoordinates z).1.im = Real.log z.im := by
  simp [initialLogCoordinates]

lemma exists_angularLocalization
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε)
    (hε0 : ε ≤ logAngleSq κ (initialLogCoordinates z) 0) :
    Nonempty (AngularLocalization B hm κ z u ε) := by
  let η₀ := Real.log z.im
  let lo := η₀ - u / (2 * ε) - 1
  let hi := η₀ + 1
  have hule : 0 ≤ u / (2 * ε) := by positivity
  have hle : lo ≤ hi := by dsimp [lo, hi]; linarith
  obtain ⟨c⟩ := exists_clippedLogSolution B hm hBm hBc κ lo hi hle (initialLogCoordinates z)
  let a := 4 * ε ^ 2 / Real.exp (2 * η₀)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (u / a)
  have hT : u < (4 * ε ^ 2 / Real.exp (2 * (initialLogCoordinates z).1.im)) * ((N : ℝ≥0) : ℝ) := by
    rw [initialLogCoordinates_im]
    have hh := (div_lt_iff₀ ha).mp hN
    simpa only [NNReal.coe_natCast, mul_comm (N : ℝ) a] using hh
  obtain ⟨τ, hτ, ht, hin, hpre, hbound, _, _⟩ := c.finite_angular_law
    hB hBm hBc hB0 hκ hκ8 rfl u ε hu hε hε0
    (by rw [initialLogCoordinates_im]; dsimp [lo, η₀]; linarith)
    (by rw [initialLogCoordinates_im]; dsimp [hi, η₀]; linarith) (N : ℝ≥0) hT
  exact ⟨⟨lo, hi, hle, c, N, τ, hτ, fun ω => (ht ω).le,
    by simpa only [initialLogCoordinates_im] using hin,
    by simpa only [initialLogCoordinates_im] using hpre,
    by simpa only [initialLogCoordinates_im] using hbound⟩⟩

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma chart_identification
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    z ∈ survivingDomain γ (a.τ ω) ∧
      ∀ t : ℝ≥0, t ≤ a.τ ω → a.solution.Q t ω = logLoewnerCoordinates G z t := by
  have hQd (s : ℝ) (hs : s ∈ Icc 0 (a.τ ω : ℝ)) := (a.solution.derivative ω s hs.1).mono
    (show Icc (0 : ℝ) (a.τ ω : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
  have hQb (s : ℝ) (hs : s ∈ Icc 0 (a.τ ω : ℝ)) : (a.solution.Q s ω).1.im ∈ Icc a.lo a.hi := by
    have hh := (a.inside ω s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)).2.2
    simpa only [Set.mem_Icc, Real.coe_toNNReal _ hs.1] using hh
  obtain ⟨hlive, heq⟩ := clipped_log_identification ((hBc ω).const_mul _) hw z hz (a.τ ω)
    a.lo a.hi a.le (fun s => a.solution.Q s ω) (a.solution.initial ω) hQd hQb
  exact ⟨hlive, fun t ht => by simpa only [Real.toNNReal_coe] using heq ⟨t.coe_nonneg, ht⟩⟩

lemma clock_eq_chart
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (t : ℝ≥0) (ht : t ≤ a.τ ω) :
    logRadiusClock (Real.log z.im) (a.solution.Q t ω) =
      Real.log ((2 * z.im) / fullRadius G t z) := by
  obtain ⟨hl, he⟩ := a.chart_identification hBc hz ω γ G F hw
  rw [he t ht]
  exact logRadiusClock_logCoordinates ((hBc ω).const_mul _) hw z t (survivingDomain_antitone γ ht hl)

lemma clock_stopped_measurable :
    Measurable[a.stopping.measurableSpace]
      (fun ω => logRadiusClock (Real.log z.im) (a.solution.Q (a.τ ω) ω)) := by
  have hQa : StronglyAdapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => a.solution.Q t) := fun t => (a.solution.adapted t).stronglyMeasurable
  have hQc (ω : Ω) : Continuous (fun t : ℝ≥0 => a.solution.Q t ω) :=
    (a.solution.lipschitz ω).continuous.comp NNReal.continuous_coe
  have hQ := measurable_stoppedValue (hQa.isStronglyProgressive_of_continuous hQc) a.stopping
  have hmQ : Measurable[a.stopping.measurableSpace] (fun ω => a.solution.Q (a.τ ω) ω) := by
    exact hQ
  exact (continuous_logRadiusClock _).measurable.comp hmQ

lemma mean_green
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane) :
    Integrable (fun ω => greenLogDensity κ (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) = initialGreen κ z := by
  obtain ⟨hi, he⟩ := a.solution.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    (Real.log z.im) u a.τ a.stopping a.T a.bounded
    (fun ω t ht => ⟨(a.inside ω t ht).1, (a.inside ω t ht).2.2⟩)
  exact ⟨hi, he.trans (greenLogDensity_initial κ z hz)⟩

end AngularLocalization
end SLEExactGauge
end

 
end

end OAI

import Mathlib
import OAI.Probability.SLE.FiniteStoppedLaw
import OAI.Probability.SLE.StoppedKernels

namespace OAI

/-! Kernel Consistency for chordal SLE. -/

section
section
section
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
namespace SLEExactGauge
lemma halfPlaneGreen_derivative {f g : ℝ → ℂ} {S : Set ℝ} {t u : ℝ}
    (hf : HasDerivWithinAt f (2 / (f t - (u : ℂ))) S t)
    (hg : HasDerivWithinAt g (2 / (g t - (u : ℂ))) S t)
    (hfi : 0 < (f t).im) (hgi : 0 < (g t).im) (hne : f t ≠ g t) :
    HasDerivWithinAt (fun s => halfPlaneGreen (f s) (g s))
      (-4 * ((f t).im / ‖f t - (u : ℂ)‖ ^ 2) *
        ((g t).im / ‖g t - (u : ℂ)‖ ^ 2)) S t := by
  have hn : f t - g t ≠ 0 := sub_ne_zero.mpr hne
  have hnc : f t - conj (g t) ≠ 0 := by
    intro h
    have he := congrArg Complex.im (sub_eq_zero.mp h)
    simp only [Complex.conj_im] at he
    linarith
  have hd := hasDerivWithinAt_log_norm_div (hf.sub (hasDerivWithinAt_conj hg)) (hf.sub hg) hnc hn
  apply hd.congr_deriv
  have h₁ : f t - conj (g t) = (f t - (u : ℂ)) - conj (g t - (u : ℂ)) := by
    simp only [map_sub, Complex.conj_ofReal]
    ring
  have h₂ : f t - g t = (f t - (u : ℂ)) - (g t - (u : ℂ)) := by ring
  change ((2 / (f t - (u : ℂ)) - conj (2 / (g t - (u : ℂ)))) / (f t - conj (g t)) -
    (2 / (f t - (u : ℂ)) - 2 / (g t - (u : ℂ))) / (f t - g t)).re = _
  rw [h₁, h₂, green_decrease_algebra _ _ (by simpa using hfi) (by simpa using hgi)
    (sub_left_inj.not.mpr hne)]
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]

 

theorem IsCapacityTwoWitness.green_kernel_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z w : ℂ)
    (hz : z ∈ survivingDomain γ t) (hw' : w ∈ survivingDomain γ t) (hne : z ≠ w) :
    HasDerivWithinAt (fun s : ℝ => halfPlaneGreen (G (Real.toNNReal s) z) (G (Real.toNNReal s) w))
      (-4 * ((G t z).im / ‖G t z - (U t : ℂ)‖ ^ 2) *
        ((G t w).im / ‖G t w - (U t : ℂ)‖ ^ 2)) (Ici 0) (t : ℝ) := by
  rcases hw with ⟨hc, h0, him, hG, hF, hGmap, hFmap, hinv, hinv', hinit, hode, hnorm, htip⟩
  have hneq : G t z ≠ G t w := by
    intro he
    apply hne
    rw [← hinv t z hz, he, hinv t w hw']
  simpa only [Real.toNNReal_coe] using halfPlaneGreen_derivative
    (f := fun s => G (Real.toNNReal s) z) (g := fun s => G (Real.toNNReal s) w)
    (S := Ici 0) (t := (t : ℝ)) (u := U t)
    (by simpa only [Real.toNNReal_coe] using hode t z hz)
    (by simpa only [Real.toNNReal_coe] using hode t w hw')
    (by simpa only [Real.toNNReal_coe, upperHalfPlane, Set.mem_ofPred_eq] using hGmap t hz)
    (by simpa only [Real.toNNReal_coe, upperHalfPlane, Set.mem_ofPred_eq] using hGmap t hw')
    (by simpa only [Real.toNNReal_coe] using hneq)

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal NNReal ComplexConjugate
namespace SLEExactGauge

lemma diskToHalfPlane_halfPlaneToDisk {w v : ℂ} (hw : 0 < w.im) (hv : 0 < v.im) :
    diskToHalfPlane w (halfPlaneToDisk w v) = v := by
  have hd := halfPlane_denominator_ne hw hv
  have hζ := halfPlaneToDisk_maps hw hv
  have he := disk_denominator_ne hζ
  unfold diskToHalfPlane
  apply (div_eq_iff he).mpr
  unfold halfPlaneToDisk
  field_simp [hd]
  ring

lemma halfPlaneGreen_eq_disk (z w : ℂ) :
    halfPlaneGreen z w = -Real.log ‖halfPlaneToDisk z w‖ := by
  have hn : ‖z - conj w‖ = ‖w - conj z‖ := by
    calc
      _ = ‖conj (z - conj w)‖ := (Complex.norm_conj _).symm
      _ = ‖-(w - conj z)‖ := by congr 1; simp only [map_sub, Complex.conj_conj]; ring
      _ = _ := norm_neg _
  rw [halfPlaneGreen, halfPlaneToDisk, Complex.star_def, norm_div, norm_div,
    hn, norm_sub_rev z w, ← Real.log_inv, inv_div]

lemma halfPlaneGreen_nonneg {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 ≤ halfPlaneGreen z w := by
  rw [halfPlaneGreen_eq_disk]
  exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (upper_mobius_norm_lt_one hw hz).le)

 

lemma halfplane_boundary_layer_green_le {D : Set ℂ} {G F : ℂ → ℂ}
    (hD : IsOpen D) (hfront : (frontier D).Nonempty)
    (hG : DifferentiableOn ℂ G D) (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hGm : MapsTo G D upperHalfPlane) (hFm : MapsTo F upperHalfPlane D)
    (hFG : ∀ w ∈ D, F (G w) = w) (hGF : ∀ w ∈ upperHalfPlane, G (F w) = w)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ D) :
    (∫⁻ w in {w | w ∈ D ∧ infDist w (frontier D) ≤ r},
      ENNReal.ofReal (halfPlaneGreen (G z) (G w))) ≤
      ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
  let f := F ∘ diskToHalfPlane (G z)
  let g := halfPlaneToDisk (G z) ∘ G
  have hz' : 0 < (G z).im := hGm hz
  have hf : DifferentiableOn ℂ f (ball 0 1) :=
    hF.comp (diskToHalfPlane_differentiable _) (diskToHalfPlane_maps hz')
  have hg : DifferentiableOn ℂ g D := (halfPlaneToDisk_differentiable hz').comp hG hGm
  have hfm : MapsTo f (ball 0 1) D := hFm.comp (diskToHalfPlane_maps hz')
  have hgm : MapsTo g D (ball 0 1) := (halfPlaneToDisk_maps hz').comp hGm
  have hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w := by
    intro w hw
    dsimp only [g, f, Function.comp_apply]
    rw [hGF _ (diskToHalfPlane_maps hz' hw), halfPlaneToDisk_diskToHalfPlane hz' hw]
  have hfg : ∀ w ∈ D, f (g w) = w := by
    intro w hw
    dsimp only [g, f, Function.comp_apply]
    rw [diskToHalfPlane_halfPlaneToDisk hz' (hGm hw), hFG w hw]
  have hh := centered_boundary_layer_green_le hD hfront hf hg hfm hgm hgf hfg hr
  simpa only [g, Function.comp_apply, ← halfPlaneGreen_eq_disk] using hh

 

theorem IsCapacityTwoWitness.boundary_layer_green
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : z ∈ survivingDomain γ t) :
    (∫⁻ w in {w | w ∈ survivingDomain γ t ∧ infDist w (frontier (survivingDomain γ t)) ≤ r},
      ENNReal.ofReal (halfPlaneGreen (G t z) (G t w))) ≤
      ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
  have hD := isOpen_survivingDomain hw.1 t
  have hDne : survivingDomain γ t ≠ univ := by
    intro he
    have h0 : (0 : ℂ) ∈ survivingDomain γ t := by rw [he]; exact mem_univ _
    exact (lt_irrefl (0 : ℝ)) h0.1.1
  have hfront : (frontier (survivingDomain γ t)).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨z, hz⟩, hDne⟩
  rcases hw with ⟨hc, h0, him, hG, hF, hGmap, hFmap, hinv, hinv', hrest⟩
  exact halfplane_boundary_layer_green_le hD hfront (hG t) (hF t) (hGmap t) (hFmap t)
    (hinv t) (hinv' t) hr hz

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def chartPoissonRate (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ)
    (t : ℝ≥0) (z : ℂ) : ℝ := (G t z).im / ‖G t z - (U t : ℂ)‖ ^ 2

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.poissonRate_continuousOn
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    ContinuousOn (fun t : ℝ => chartPoissonRate U G t.toNNReal z) (Icc 0 (T : ℝ)) := by
  have hc := h.time_continuousOn T z hz
  have huc : Continuous (fun t : ℝ => (U t.toNNReal : ℂ)) :=
    Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)
  exact (Complex.continuous_im.comp_continuousOn hc).div
    ((hc.sub huc.continuousOn).norm.pow 2)
    (fun t ht => pow_ne_zero 2 (norm_ne_zero_iff.mpr
      (h.centered_ne_zero _ z (h.live_at_real_time T z hz t ht.2))))

lemma IsCapacityTwoWitness.poissonRate_nonneg
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) : 0 ≤ chartPoissonRate U G t z :=
  div_nonneg (h.imag_positive t z hz).le (sq_nonneg _)

lemma IsCapacityTwoWitness.green_pair_integral
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (s T : ℝ≥0) (hsT : s ≤ T) (z w : ℂ)
    (hz : z ∈ survivingDomain γ T) (hw : w ∈ survivingDomain γ T) (hne : z ≠ w) :
    4 * (∫ t in (s : ℝ)..(T : ℝ),
      chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w) =
      halfPlaneGreen (G s z) (G s w) - halfPlaneGreen (G T z) (G T w) := by
  have hsub : Icc (s : ℝ) (T : ℝ) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc s.coe_nonneg le_rfl
  have hab : (s : ℝ) ≤ T := hsT
  let K : ℝ → ℝ := fun t => halfPlaneGreen (G t.toNNReal z) (G t.toNNReal w)
  let R : ℝ → ℝ := fun t => chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w
  have hr : ContinuousOn R (Icc (s : ℝ) (T : ℝ)) :=
    ((h.poissonRate_continuousOn hU T z hz).mul (h.poissonRate_continuousOn hU T w hw)).mono hsub
  have hd : ∀ t ∈ Icc (s : ℝ) (T : ℝ), HasDerivWithinAt K (-4 * R t) (Ici 0) t := by
    intro t ht
    have ht0 : 0 ≤ t := s.coe_nonneg.trans ht.1
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have hh := h.green_kernel_derivative t.toNNReal z w
      (survivingDomain_antitone γ htT hz) (survivingDomain_antitone γ htT hw) hne
    simpa only [K, R, chartPoissonRate, Real.coe_toNNReal _ ht0, mul_assoc] using hh
  have hc : ContinuousOn K (Icc (s : ℝ) (T : ℝ)) := by
    intro t ht
    exact ((hd t ht).mono (fun x hx => le_trans s.coe_nonneg hx.1)).continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hc
    (fun t ht => (hd t ⟨ht.1.le, ht.2.le⟩).mono (fun x hx =>
      le_trans (s.coe_nonneg.trans ht.1.le) hx.le))
    ((continuousOn_const.mul hr).intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_const_mul] at he
  dsimp only [K] at he
  simp only [Real.toNNReal_coe] at he
  change -4 * (∫ t in (s : ℝ)..(T : ℝ), R t) = _ at he
  change 4 * (∫ t in (s : ℝ)..(T : ℝ), R t) = _
  linarith

 

theorem IsCapacityTwoWitness.green_pair_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (s T : ℝ≥0) (hsT : s ≤ T) (z w : ℂ)
    (hz : z ∈ survivingDomain γ T) (hw : w ∈ survivingDomain γ T) (hne : z ≠ w) :
    (∫ t in (s : ℝ)..(T : ℝ),
      chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w) ≤
      halfPlaneGreen (G s z) (G s w) / 4 := by
  have he := h.green_pair_integral hU s T hsT z w hz hw hne
  have hp := halfPlaneGreen_nonneg (h.imag_positive T z hz) (h.imag_positive T w hw)
  linarith

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma lintegral_lower_interval_le (a : ℝ) (S : Set ℝ) (f : ℝ → ℝ≥0∞)
    (C : ℝ≥0∞) (hS : S ⊆ Ici a)
    (hdown : ∀ T ∈ S, Icc a T ⊆ S)
    (hbound : ∀ T ∈ S, (∫⁻ t in Icc a T, f t) ≤ C) :
    (∫⁻ t in S, f t) ≤ C := by
  classical
  by_cases hmax : ∃ T ∈ S, ∀ t ∈ S, t ≤ T
  · obtain ⟨T, hT, hmax⟩ := hmax
    exact (lintegral_mono_set (show S ⊆ Icc a T from fun t ht => ⟨hS ht, hmax t ht⟩)).trans (hbound T hT)
  · let Q := {q : ℚ | (q : ℝ) ∈ S}
    have hcover : S = ⋃ q : Q, Icc a (q : ℝ) := by
      ext t
      constructor
      · intro ht
        have hex : ∃ u ∈ S, t < u := by
          by_contra hh
          apply hmax
          refine ⟨t, ht, ?_⟩
          intro u hu
          exact le_of_not_gt (fun h => hh ⟨u, hu, h⟩)
        obtain ⟨u, hu, htu⟩ := hex
        obtain ⟨q, htq, hqu⟩ := exists_rat_btwn htu
        have hq : q ∈ Q := hdown u hu ⟨(hS ht).trans htq.le, hqu.le⟩
        exact mem_iUnion.mpr ⟨⟨q, hq⟩, ⟨hS ht, htq.le⟩⟩
      · intro ht
        obtain ⟨q, hq⟩ := mem_iUnion.mp ht
        exact hdown (q : ℝ) q.property hq
    have hd : Directed (· ⊆ ·) (fun q : Q => Icc a (q : ℝ)) := by
      intro q r
      rcases le_total (q : ℝ) (r : ℝ) with hqr | hrq
      · exact ⟨r, Icc_subset_Icc le_rfl hqr, Subset.rfl⟩
      · exact ⟨q, Subset.rfl, Icc_subset_Icc le_rfl hrq⟩
    rw [hcover, setLIntegral_iUnion_of_directed f hd]
    exact iSup_le (fun q => hbound _ q.property)

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

 

theorem IsCapacityTwoWitness.live_green_pair_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (s : ℝ≥0) (z w : ℂ) (hne : z ≠ w) :
    (∫⁻ t in {t : ℝ | (s : ℝ) ≤ t ∧ z ∈ survivingDomain γ t.toNNReal ∧
      w ∈ survivingDomain γ t.toNNReal},
      ENNReal.ofReal (chartPoissonRate U G t.toNNReal z *
        chartPoissonRate U G t.toNNReal w)) ≤
      ENNReal.ofReal (halfPlaneGreen (G s z) (G s w) / 4) := by
  apply lintegral_lower_interval_le
  · exact fun _ ht => ht.1
  · intro T hT t ht
    have hle : t.toNNReal ≤ T.toNNReal := Real.toNNReal_mono ht.2
    exact ⟨ht.1, survivingDomain_antitone γ hle hT.2.1,
      survivingDomain_antitone γ hle hT.2.2⟩
  · intro T hT
    have hT0 : 0 ≤ T := s.coe_nonneg.trans hT.1
    have hsT : s ≤ T.toNNReal := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hT0]
      exact hT.1
    let R : ℝ → ℝ := fun t => chartPoissonRate U G t.toNNReal z *
      chartPoissonRate U G t.toNNReal w
    have hc : ContinuousOn R (Icc (s : ℝ) T) := by
      have hh := (h.poissonRate_continuousOn hU T.toNNReal z hT.2.1).mul
        (h.poissonRate_continuousOn hU T.toNNReal w hT.2.2)
      rw [Real.coe_toNNReal _ hT0] at hh
      exact hh.mono (Icc_subset_Icc s.coe_nonneg le_rfl)
    have hn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc (s : ℝ) T)] R := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hle := Real.toNNReal_mono ht.2
      exact mul_nonneg
        (h.poissonRate_nonneg _ z (survivingDomain_antitone γ hle hT.2.1))
        (h.poissonRate_nonneg _ w (survivingDomain_antitone γ hle hT.2.2))
    change (∫⁻ t in Icc (s : ℝ) T, ENNReal.ofReal (R t)) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc) hn]
    apply ENNReal.ofReal_le_ofReal
    have hb := h.green_pair_bound hU s T.toNNReal hsT z w hT.2.1 hT.2.2 hne
    rw [Real.coe_toNNReal _ hT0, intervalIntegral.integral_of_le hT.1,
      ← integral_Icc_eq_integral_Ioc] at hb
    exact hb

end SLEExactGauge

end

 
section

open Set Filter Metric MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def greenBrownianCoefficient (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  Real.sqrt κ * greenExponent κ * (G t z - (U t : ℂ)).re /
    ‖G t z - (U t : ℂ)‖ ^ 2 * greenDensity κ U γ G t z

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma greenExponent_ge_one {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    1 ≤ greenExponent κ := by
  unfold greenExponent
  have : (2 : ℝ) ≤ 8 / κ := (le_div_iff₀ hκ).mpr (by linarith)
  linarith

 

lemma IsCapacityTwoWitness.green_coefficient_le_poisson
    (h : IsCapacityTwoWitness U γ G F) (_hU : Continuous U)
    {κ r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hr : 0 < r)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (hR : r ≤ fullRadius G t z) :
    |greenBrownianCoefficient κ U γ G t z| ≤
      (Real.sqrt κ * greenExponent κ * r ^ (-codimension κ)) *
        chartPoissonRate U G t z := by
  let Z := G t z - (U t : ℂ)
  have hn : 0 < ‖Z‖ := norm_pos_iff.mpr (h.centered_ne_zero t z hz)
  have hi : 0 < Z.im := by
    simpa only [Z, Complex.sub_im, Complex.ofReal_im, sub_zero] using h.imag_positive t z hz
  have hs : 0 ≤ Real.sin Z.arg := by rw [Complex.sin_arg]; positivity
  have hs1 : Real.sin Z.arg ≤ 1 := Real.sin_le_one _
  have hp : 0 ≤ codimension κ := by unfold codimension dimension; linarith
  have ha := greenExponent_ge_one hκ hκ4
  have hM : greenDensity κ U γ G t z ≤
      r ^ (-codimension κ) * (Z.im / ‖Z‖) := by
    rw [greenDensity, ite_eq_left hz]
    change fullRadius G t z ^ (-codimension κ) * (Real.sin Z.arg) ^ greenExponent κ ≤ _
    calc
      _ ≤ r ^ (-codimension κ) * Real.sin Z.arg :=
        mul_le_mul (Real.rpow_le_rpow_of_nonpos hr hR (neg_nonpos.mpr hp))
          (Real.rpow_le_self_of_le_one hs hs1 ha) (Real.rpow_nonneg hs _)
          (Real.rpow_nonneg hr.le _)
      _ = _ := by rw [Complex.sin_arg]
  have hMn : 0 ≤ greenDensity κ U γ G t z := greenDensity_nonneg h κ t z
  have hX : |Z.re| ≤ ‖Z‖ := Complex.abs_re_le_norm Z
  have hC : 0 ≤ Real.sqrt κ * greenExponent κ := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  change |Real.sqrt κ * greenExponent κ * Z.re / ‖Z‖ ^ 2 *
    greenDensity κ U γ G t z| ≤ _
  rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hC, show |‖Z‖ ^ 2| = ‖Z‖ ^ 2 from abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg hMn]
  calc
    _ ≤ (Real.sqrt κ * greenExponent κ * ‖Z‖ / ‖Z‖ ^ 2) *
        (r ^ (-codimension κ) * (Z.im / ‖Z‖)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hX hC) (sq_nonneg _)
      · exact hM
      · exact hMn
      · positivity
    _ = (Real.sqrt κ * greenExponent κ * r ^ (-codimension κ)) *
        chartPoissonRate U G t z := by
      have hZi : Z.im = (G t z).im := by simp [Z]
      unfold chartPoissonRate
      change _ = (Real.sqrt κ * greenExponent κ * r ^ (-codimension κ)) *
        ((G t z).im / ‖Z‖ ^ 2)
      rw [hZi]
      field_simp

 

lemma surviving_frontier_distance_le_past
    (t a : ℝ≥0) (hat : a ≤ t) (z : ℂ) (hz : z ∈ survivingDomain γ t) :
    infDist z (frontier (survivingDomain γ t)) ≤ dist (γ a) z := by
  have hn : γ a ∉ survivingDomain γ t := by
    intro ha
    exact ha.1.2 ⟨a, ⟨bot_le, hat⟩, rfl⟩
  have hDne : survivingDomain γ t ≠ univ := by
    intro he
    exact hn (he ▸ mem_univ _)
  obtain ⟨w, hw, he⟩ := exists_mem_frontier_infDist_compl_eq_dist hz hDne
  calc
    _ ≤ dist z w := infDist_le_dist_of_mem hw
    _ = infDist z (survivingDomain γ t)ᶜ := he.symm
    _ ≤ dist z (γ a) := infDist_le_dist_of_mem hn
    _ = _ := dist_comm _ _

 

lemma IsCapacityTwoWitness.radius_ge_of_no_trace_approach
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    {r : ℝ} (hr : 0 < r) (hy : r ≤ z.im)
    (havoid : ∀ a ∈ Icc 0 t, r ≤ dist (γ a) z) : r ≤ fullRadius G t z := by
  by_contra hlt
  obtain ⟨a, ha, hd⟩ := h.trace_approach_of_radius_lt hU t z hz r hr hy (lt_of_not_ge hlt)
  exact (not_lt_of_ge (havoid a ha)) hd

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}

noncomputable def physicalWeight (a : AngularLocalization B hm κ z u ε)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  greenLogDensity κ (a.solution.Q (min t (a.τ ω)) ω) (B (min t (a.τ ω)) ω)

lemma physicalWeight_bound (a : AngularLocalization B hm κ z u ε)
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) (ω : Ω) :
    0 ≤ a.physicalWeight t ω ∧ a.physicalWeight t ω ≤
      Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) :=
  ⟨greenLogDensity_nonneg _ _ _, greenLogDensity_le_radius κ _ u hκ hκ8 _ _
    (a.inside ω _ (min_le_right _ _)).1⟩

lemma physicalWeight_adapted (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    StronglyAdapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) a.physicalWeight := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hQa : StronglyAdapted f (fun t : ℝ≥0 => a.solution.Q t) :=
    fun t => (a.solution.adapted t).stronglyMeasurable
  have hBa : StronglyAdapted f B := Filtration.stronglyAdapted_natural _
  have hg : StronglyAdapted f (fun t ω => greenLogDensity κ (a.solution.Q t ω) (B t ω)) := by
    intro t
    exact (greenLogDensity_contDiff κ).continuous.comp_stronglyMeasurable ((hQa t).prodMk (hBa t))
  have hc (ω : Ω) : Continuous (fun t : ℝ≥0 => greenLogDensity κ (a.solution.Q t ω) (B t ω)) :=
    (greenLogDensity_contDiff κ).continuous.comp
      (((a.solution.lipschitz ω).continuous.comp NNReal.continuous_coe).prodMk (hBc ω))
  have hs := hg.stoppedProcess hc a.stopping
  convert hs using 1
  ext t ω
  simp only [physicalWeight, stoppedProcess, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, NNReal.coe_min]

lemma physicalWeight_integrable (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) : Integrable (a.physicalWeight t) P := by
  apply Integrable.of_bound ((a.physicalWeight_adapted hBc t).mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le t)).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (a.physicalWeight_bound hκ hκ8 t ω).1]
  exact (a.physicalWeight_bound hκ hκ8 t ω).2

 

theorem physicalWeight_martingale (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    Martingale a.physicalWeight (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hmA := a.physicalWeight_adapted hBc
  have hi := a.physicalWeight_integrable (P := P) hBc hκ hκ8
  refine ⟨hmA, fun s t hst => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (f.le s) (hi t)
    (fun _ _ _ => (hi s).integrableOn) _ (hmA s).aestronglyMeasurable
  intro A hA _
  let σ (ω : Ω) : ℝ≥0 := if ω ∈ A then t else s
  have hσ : IsStoppingTime f (fun ω => (σ ω : WithTop ℝ≥0)) := by
    apply stopping_paste_after f (isStoppingTime_const f s) (isStoppingTime_const f t)
      (fun _ => hst)
    change MeasurableSet[(isStoppingTime_const f s).measurableSpace] A
    rw [IsStoppingTime.measurableSpace_const]
    exact hA
  let ρ (ω : Ω) : ℝ≥0 := min (σ ω) (a.τ ω)
  have hρ : IsStoppingTime f (fun ω => (ρ ω : WithTop ℝ≥0)) := by
    simpa only [ρ, WithTop.coe_min] using hσ.min a.stopping
  have hs : IsStoppingTime f (fun ω => (min s (a.τ ω) : WithTop ℝ≥0)) := by
    simpa only [WithTop.coe_min] using (isStoppingTime_const f s).min a.stopping
  have hin (ω : Ω) (v : ℝ≥0) (hv : v ≤ a.τ ω) :
      logRadiusClock (Real.log z.im) (a.solution.Q v ω) ≤ u ∧
        a.lo ≤ (a.solution.Q v ω).1.im ∧ (a.solution.Q v ω).1.im ≤ a.hi :=
    ⟨(a.inside ω v hv).1, (a.inside ω v hv).2.2⟩
  obtain ⟨hri, hre⟩ := a.solution.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    (Real.log z.im) u ρ hρ a.T (fun ω => (min_le_right _ _).trans (a.bounded ω))
    (fun ω v hv => hin ω v (hv.trans (min_le_right _ _)))
  obtain ⟨hsi, hse⟩ := a.solution.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    (Real.log z.im) u (fun ω => min s (a.τ ω)) hs a.T
    (fun ω => (min_le_right _ _).trans (a.bounded ω))
    (fun ω v hv => hin ω v (hv.trans (min_le_right _ _)))
  have he (ω : Ω) :
      greenLogDensity κ (a.solution.Q (ρ ω) ω) (B (ρ ω) ω) - a.physicalWeight s ω =
        A.indicator (fun ω => a.physicalWeight t ω - a.physicalWeight s ω) ω := by
    by_cases hω : ω ∈ A <;> simp [physicalWeight, ρ, σ, hω]
  have heI : (∫ ω, A.indicator (fun ω => a.physicalWeight t ω - a.physicalWeight s ω) ω ∂P) = 0 := by
    simp_rw [← he]
    rw [integral_sub hri (hi s)]
    change (∫ ω, greenLogDensity κ (a.solution.Q (ρ ω) ω) (B (ρ ω) ω) ∂P) -
      (∫ ω, greenLogDensity κ (a.solution.Q (min s (a.τ ω)) ω) (B (min s (a.τ ω)) ω) ∂P) = 0
    have hse' : (∫ ω, greenLogDensity κ (a.solution.Q (min (s : ℝ) (a.τ ω)) ω)
        (B (min s (a.τ ω)) ω) ∂P) = greenLogDensity κ (initialLogCoordinates z) 0 := by
      simpa only [NNReal.coe_min] using hse
    rw [hre, hse', sub_self]
  rw [integral_indicator (f.le s _ hA), integral_sub (hi t).integrableOn (hi s).integrableOn] at heI
  exact (sub_eq_zero.mp heI).symm

end AngularLocalization
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε δ : ℝ}

lemma stopping_le_of_hit (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v δ) (huv : u ≤ v) (ω : Ω)
    (hb : ω ∈ b.hit) : a.τ ω ≤ b.τ ω := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have he := a.synchronize b ω (b.τ ω) hlt.le le_rfl
  have hh := (a.before ω _ hlt).1
  rw [he, show logRadiusClock (Real.log z.im) (b.solution.Q (b.τ ω) ω) = v from hb] at hh
  exact (not_lt_of_ge huv) hh

lemma power_stopped_measurable (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (p α : ℝ) :
    Measurable[a.stopping.measurableSpace]
      (fun ω => powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)) := by
  have hQa : StronglyAdapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => a.solution.Q t) := fun t => (a.solution.adapted t).stronglyMeasurable
  have hQc (ω : Ω) : Continuous (fun t : ℝ≥0 => a.solution.Q t ω) :=
    (a.solution.lipschitz ω).continuous.comp NNReal.continuous_coe
  have hmQ : Measurable[a.stopping.measurableSpace] (fun ω => a.solution.Q (a.τ ω) ω) :=
    measurable_stoppedValue (hQa.isStronglyProgressive_of_continuous hQc) a.stopping
  have hBa : StronglyAdapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) B :=
    Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)
  have hmB : Measurable[a.stopping.measurableSpace] (fun ω => B (a.τ ω) ω) :=
    measurable_stoppedValue (hBa.isStronglyProgressive_of_continuous hBc) a.stopping
  exact (powerLogDensity_contDiff κ p α).continuous.measurable.comp (hmQ.prodMk hmB)

lemma radiusKernel_terminal (a : AngularLocalization B hm κ z u ε) (p α : ℝ) (ω : Ω) :
    a.radiusKernel p α u ω = a.hit.indicator
      (fun ω => powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)) ω := by
  have hc : a.clock.S (a.τ ω) ω ≤ u := (a.inside ω _ le_rfl).1
  by_cases hh : ω ∈ a.hit
  · have he : a.clock.S (a.τ ω) ω = u := hh
    have hi : a.clock.inverse u ω = (a.τ ω : ℝ) := by
      simpa only [he] using a.clock.inverse_clock ω (a.τ ω) ⟨(a.τ ω).coe_nonneg, le_rfl⟩
    rw [radiusKernel, ite_eq_left he.ge, radiusValue, hi, Real.toNNReal_coe, indicator_of_mem hh]
  · have hn : ¬u ≤ a.clock.S (a.τ ω) ω := by
      intro h
      exact hh (le_antisymm hc h)
    rw [radiusKernel, ite_eq_right hn, indicator_of_notMem hh]

end AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v : ℝ} {ε : ℕ → ℝ}

lemma localization_le_radiusStop (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (n : ℕ) : (fun ω => ((a n).τ ω : WithTop ℝ≥0)) ≤ localizedRadiusStop a := by
  intro ω
  apply le_iInf
  intro m
  unfold AngularLocalization.hitTime
  split_ifs with hm'
  · exact WithTop.coe_le_coe.mpr ((a n).stopping_le_of_hit (a m) le_rfl ω hm')
  · exact le_top

lemma localizedRadiusStop_mono
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n)) (huv : u ≤ v) :
    localizedRadiusStop a ≤ localizedRadiusStop b := by
  intro ω
  apply le_iInf
  intro n
  unfold AngularLocalization.hitTime
  split_ifs with hn
  · have hc := (a n).terminal_clock_min (b n) huv ω
    have hb : (b n).clock.S ((b n).τ ω) ω = v := hn
    rw [hb, min_eq_left huv] at hc
    rw [localizedRadiusStop_eq_hit a ω n hc]
    exact WithTop.coe_le_coe.mpr ((a n).stopping_le (b n) huv le_rfl ω)
  · exact le_top

lemma limitRadiusKernel_terminal_measurable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hu : 0 ≤ u) (p α : ℝ) :
    Measurable[(localizedRadiusStop_stopping a).measurableSpace] (limitRadiusKernel a p α u) := by
  apply @measurable_of_tendsto_metrizable Ω ℝ
    (localizedRadiusStop_stopping a).measurableSpace _ _ _ _
    (fun n ω => (a n).radiusKernel p α u ω)
  · intro n
    have he : (a n).radiusKernel p α u = (a n).hit.indicator
        (fun ω => powerLogDensity κ p α ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω)) :=
      funext ((a n).radiusKernel_terminal p α)
    rw [he]
    exact (((a n).power_stopped_measurable hBc p α).indicator (a n).measurable_hit).mono
      ((a n).stopping.measurableSpace_mono (localizedRadiusStop_stopping a)
        (localization_le_radiusStop a n)) le_rfl
  · apply tendsto_pi_nhds.mpr
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [radiusKernel_eventually_limit a hε p α u ω] with n hn
    simpa only [max_eq_left hu] using hn.symm

 
noncomputable def radiusFiltration
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n)) : Filtration ℝ≥0 mΩ where
  seq u := (localizedRadiusStop_stopping (a u)).measurableSpace
  mono' u v huv := (localizedRadiusStop_stopping (a u)).measurableSpace_mono
    (localizedRadiusStop_stopping (a v)) (localizedRadiusStop_mono (a u) (a v) (by exact_mod_cast huv))
  le' u := (localizedRadiusStop_stopping (a u)).measurableSpace_le

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

end SLEExactGauge
end
end
end

end OAI

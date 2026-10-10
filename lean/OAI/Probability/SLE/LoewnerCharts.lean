import Mathlib
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI

/-! Loewner Charts for chordal SLE. -/

section
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 
def upperHalfPlane : Set ℂ := {z | 0 < z.im}

 

def survivingDomain (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : Set ℂ :=
  {z | z ∈ upperHalfPlane \ (γ '' Icc 0 t) ∧
    ¬ Bornology.IsBounded (connectedComponentIn (upperHalfPlane \ (γ '' Icc 0 t)) z)}

 

def IsCapacityTwoWitness (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G F : ℝ≥0 → ℂ → ℂ) : Prop :=
  Continuous γ ∧ γ 0 = 0 ∧ (∀ t, 0 ≤ (γ t).im) ∧
    (∀ t, DifferentiableOn ℂ (G t) (survivingDomain γ t)) ∧
    (∀ t, DifferentiableOn ℂ (F t) upperHalfPlane) ∧
    (∀ t, MapsTo (G t) (survivingDomain γ t) upperHalfPlane) ∧
    (∀ t, MapsTo (F t) upperHalfPlane (survivingDomain γ t)) ∧
    (∀ t z, z ∈ survivingDomain γ t → F t (G t z) = z) ∧
    (∀ t z, z ∈ upperHalfPlane → G t (F t z) = z) ∧
    (∀ z ∈ upperHalfPlane, G 0 z = z) ∧
    (∀ t z, z ∈ survivingDomain γ t →
      HasDerivWithinAt (fun u : ℝ => G (Real.toNNReal u) z)
        (2 / (G t z - (U t : ℂ))) (Ici 0) (t : ℝ)) ∧
    (∀ t, Tendsto (fun z : ℂ => z * (G t z - z))
      (cocompact ℂ ⊓ 𝓟 (survivingDomain γ t)) (𝓝 (2 * (t : ℂ)))) ∧
    (∀ t, Tendsto (fun y : ℝ => F t ((U t : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (γ t)))

lemma survivingDomain_antitone (γ : ℝ≥0 → ℂ) : Antitone (survivingDomain γ) := by
  intro s t hst z hz
  have hpast : γ '' Icc 0 s ⊆ γ '' Icc 0 t := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨hu.1, hu.2.trans hst⟩, rfl⟩
  have hb : upperHalfPlane \ (γ '' Icc 0 t) ⊆ upperHalfPlane \ (γ '' Icc 0 s) := by
    intro w hw
    exact ⟨hw.1, fun hh => hw.2 (hpast hh)⟩
  exact ⟨hb hz.1, fun hbounded => hz.2 (hbounded.subset (connectedComponentIn_mono z hb))⟩

lemma isOpen_upperHalfPlane : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im

lemma isOpen_survivingDomain {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (t : ℝ≥0) :
    IsOpen (survivingDomain γ t) := by
  have hb : IsOpen (upperHalfPlane \ (γ '' Icc 0 t)) :=
    isOpen_upperHalfPlane.sdiff (isCompact_Icc.image hγ).isClosed
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  refine ⟨connectedComponentIn (upperHalfPlane \ (γ '' Icc 0 t)) z, ?_,
    hb.connectedComponentIn, mem_connectedComponentIn hz.1⟩
  intro w hw
  refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
  rw [← connectedComponentIn_eq hw]
  exact hz.2

lemma IsCapacityTwoWitness.time_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => G v.toNNReal z)
      (2 / (G u.toNNReal z - (U u.toNNReal : ℂ))) (Icc 0 (T : ℝ)) u := by
  rcases h with ⟨hγ, hγ0, hγim, hG, hF, hGmap, hFmap, hinv, hinv', h0, hode, hnorm, htip⟩
  have hlu : u.toNNReal ≤ T := by
    exact_mod_cast (show (u.toNNReal : ℝ) ≤ (T : ℝ) by rw [Real.coe_toNNReal _ hu.1]; exact hu.2)
  have hh := (hode u.toNNReal z (survivingDomain_antitone γ hlu hz)).mono
    (show Icc (0 : ℝ) T ⊆ Ici 0 from Icc_subset_Ici_self)
  simpa only [Real.coe_toNNReal _ hu.1] using hh

lemma IsCapacityTwoWitness.time_continuousOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) :
    ContinuousOn (fun v : ℝ => G v.toNNReal z) (Icc 0 (T : ℝ)) :=
  fun u hu => (h.time_derivative T z hz u hu).continuousWithinAt

lemma IsCapacityTwoWitness.imag_positive
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) : 0 < (G t z).im := h.2.2.2.2.2.1 t hz

lemma IsCapacityTwoWitness.centered_ne_zero
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) : G t z - (U t : ℂ) ≠ 0 := by
  intro hh
  have hi := congrArg Complex.im hh
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  exact (h.imag_positive t z hz).ne' hi

lemma IsCapacityTwoWitness.imag_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => (G v.toNNReal z).im)
      (-2 * (G u.toNNReal z).im / Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ)))
      (Icc 0 (T : ℝ)) u := by
  have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt u (h.time_derivative T z hz u hu)
  simpa [Function.comp_def, Complex.div_im, neg_div] using hh

lemma IsCapacityTwoWitness.imag_antitoneOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) :
    AntitoneOn (fun v : ℝ => (G v.toNNReal z).im) (Icc 0 (T : ℝ)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (Complex.continuous_im.comp_continuousOn (h.time_continuousOn T z hz))
    (fun u hu => (h.imag_derivative T z hz u (interior_subset hu)).mono interior_subset)
  intro u hu
  have hu' : u ∈ Icc 0 (T : ℝ) := interior_subset hu
  have hle : u.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe).mpr hu'.2
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (h.imag_positive u.toNNReal z (survivingDomain_antitone γ hle hz)).le)
    (Complex.normSq_nonneg _)

 

lemma complex_linear_ode_exp (T : ℝ) (hT : 0 ≤ T) (f c : ℝ → ℂ)
    (hc : ContinuousOn c (Icc 0 T))
    (hf : ∀ u ∈ Icc 0 T, HasDerivWithinAt f (c u * f u) (Icc 0 T) u) :
    f T = f 0 * Complex.exp (∫ u in (0 : ℝ)..T, c u) := by
  by_cases hT0 : T = 0
  · simp [hT0]
  have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  let C (u : ℝ) : ℂ := c (projIcc 0 T hT u)
  have hC : Continuous C := hc.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun u => (projIcc 0 T hT u).property)
  have hCc (u : ℝ) (hu : u ∈ Icc 0 T) : C u = c u := by simp only [C, projIcc_of_mem hT hu]
  let I (u : ℝ) : ℂ := ∫ v in (0 : ℝ)..u, C v
  have hI (u : ℝ) : HasDerivAt I (C u) u :=
    intervalIntegral.integral_hasDerivAt_right (hC.intervalIntegrable _ _)
      hC.aestronglyMeasurable.stronglyMeasurableAtFilter hC.continuousAt
  have hd (u : ℝ) (hu : u ∈ Icc 0 T) :
      HasDerivWithinAt (fun v => f v * Complex.exp (-I v)) 0 (Icc 0 T) u := by
    convert (hf u hu).mul ((hI u).neg.cexp.hasDerivWithinAt) using 1
    try rfl
    rw [hCc u hu]
    ring
  have hid : ∀ u ∈ Icc 0 T, DifferentiableWithinAt ℝ (fun v => f v * Complex.exp (-I v)) (Icc 0 T) u :=
    fun u hu => (hd u hu).differentiableWithinAt
  have he := constant_of_derivWithin_zero hid (fun u hu =>
    (hd u ⟨hu.1, hu.2.le⟩).derivWithin (uniqueDiffOn_Icc hTp u ⟨hu.1, hu.2.le⟩)) T ⟨hT, le_rfl⟩
  have hfactor : f T * Complex.exp (-I T) = f 0 := by
    simpa only [I, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, mul_one] using he
  have hInt : I T = ∫ u in (0 : ℝ)..T, c u := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact hCc u (by simpa only [uIcc_of_le hT] using hu)
  calc
    f T = (f T * Complex.exp (-I T)) * Complex.exp (I T) := by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [hfactor, hInt]

lemma IsCapacityTwoWitness.live_at_real_time
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (_h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ≤ (T : ℝ)) :
    z ∈ survivingDomain γ u.toNNReal :=
  survivingDomain_antitone γ (Real.toNNReal_le_iff_le_coe.mpr hu) hz

lemma IsCapacityTwoWitness.spatial_differentiableAt
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) : DifferentiableAt ℂ (G t) z :=
  (h.2.2.2.1 t z hz).differentiableAt ((isOpen_survivingDomain h.1 t).mem_nhds hz)

lemma IsCapacityTwoWitness.initial_value
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (z : ℂ) (hz : z ∈ upperHalfPlane) : G 0 z = z :=
  h.2.2.2.2.2.2.2.2.2.1 z hz

noncomputable def loewnerPairCoefficient
    (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ) (w z : ℂ) (u : ℝ) : ℂ :=
  (-2 : ℂ) / ((G u.toNNReal w - (U u.toNNReal : ℂ)) *
    (G u.toNNReal z - (U u.toNNReal : ℂ)))

lemma IsCapacityTwoWitness.pair_coefficient_continuousOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T) :
    ContinuousOn (loewnerPairCoefficient U G w z) (Icc 0 (T : ℝ)) := by
  have hUc : Continuous (fun u : ℝ => (U u.toNNReal : ℂ)) :=
    Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)
  exact continuousOn_const.div
    (((h.time_continuousOn T w hw).sub hUc.continuousOn).mul
      ((h.time_continuousOn T z hz).sub hUc.continuousOn))
    (fun u hu => mul_ne_zero (h.centered_ne_zero _ w (h.live_at_real_time T w hw u hu.2))
      (h.centered_ne_zero _ z (h.live_at_real_time T z hz u hu.2)))

lemma IsCapacityTwoWitness.difference_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => G v.toNNReal w - G v.toNNReal z)
      (loewnerPairCoefficient U G w z u * (G u.toNNReal w - G u.toNNReal z))
      (Icc 0 (T : ℝ)) u := by
  have hw0 := h.centered_ne_zero _ w (h.live_at_real_time T w hw u hu.2)
  have hz0 := h.centered_ne_zero _ z (h.live_at_real_time T z hz u hu.2)
  have he : loewnerPairCoefficient U G w z u * (G u.toNNReal w - G u.toNNReal z) =
      2 / (G u.toNNReal w - (U u.toNNReal : ℂ)) -
      2 / (G u.toNNReal z - (U u.toNNReal : ℂ)) := by
    unfold loewnerPairCoefficient
    field_simp
    ring
  rw [he]
  exact (h.time_derivative T w hw u hu).sub (h.time_derivative T z hz u hu)

lemma IsCapacityTwoWitness.difference_formula
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T) :
    G T w - G T z = (w - z) * Complex.exp
      (∫ u in (0 : ℝ)..(T : ℝ), loewnerPairCoefficient U G w z u) := by
  have hh := complex_linear_ode_exp (T : ℝ) T.coe_nonneg
    (fun v : ℝ => G v.toNNReal w - G v.toNNReal z)
    (loewnerPairCoefficient U G w z)
    (h.pair_coefficient_continuousOn hU T w z hw hz)
    (h.difference_derivative T w z hw hz)
  simpa only [Real.toNNReal_coe, Real.toNNReal_zero,
    h.initial_value w hw.1.1, h.initial_value z hz.1.1] using hh

lemma IsCapacityTwoWitness.imag_ge_terminal
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    (G T z).im ≤ (G u.toNNReal z).im := by
  simpa only [Real.toNNReal_coe] using h.imag_antitoneOn T z hz hu ⟨T.coe_nonneg, le_rfl⟩ hu.2

lemma IsCapacityTwoWitness.centered_norm_ge_terminal
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    (G T z).im ≤ ‖G u.toNNReal z - (U u.toNNReal : ℂ)‖ := by
  apply (h.imag_ge_terminal T z hz u hu).trans
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
    Complex.im_le_norm (G u.toNNReal z - (U u.toNNReal : ℂ))

lemma IsCapacityTwoWitness.pair_coefficient_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T)
    (c : ℝ) (hc : 0 < c) (hcw : c ≤ (G T w).im) (hcz : c ≤ (G T z).im)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    ‖loewnerPairCoefficient U G w z u‖ ≤ 2 / (c * c) := by
  have hw' := hcw.trans (h.centered_norm_ge_terminal T w hw u hu)
  have hz' := hcz.trans (h.centered_norm_ge_terminal T z hz u hu)
  unfold loewnerPairCoefficient
  rw [norm_div, norm_mul, norm_neg, Complex.norm_two]
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hc hc)
    (mul_le_mul hw' hz' hc.le (norm_nonneg _))

lemma IsCapacityTwoWitness.pair_coefficient_intervalIntegrable
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T) :
    IntervalIntegrable (loewnerPairCoefficient U G w z) volume 0 (T : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le T.coe_nonneg] using h.pair_coefficient_continuousOn hU T w z hw hz

lemma IsCapacityTwoWitness.pair_coefficient_tendsto
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ≤ (T : ℝ)) :
    Tendsto (fun w => loewnerPairCoefficient U G w z u) (𝓝 z)
      (𝓝 (loewnerPairCoefficient U G z z u)) := by
  have hzc := h.centered_ne_zero _ z (h.live_at_real_time T z hz u hu)
  have hG := (h.spatial_differentiableAt _ z (h.live_at_real_time T z hz u hu)).continuousAt
  exact tendsto_const_nhds.div ((hG.sub_const _).mul_const _) (mul_ne_zero hzc hzc)

lemma IsCapacityTwoWitness.pair_integral_tendsto
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) :
    Tendsto (fun w => ∫ u in (0 : ℝ)..(T : ℝ), loewnerPairCoefficient U G w z u) (𝓝 z)
      (𝓝 (∫ u in (0 : ℝ)..(T : ℝ), loewnerPairCoefficient U G z z u)) := by
  let c : ℝ := (G T z).im / 2
  have hp := h.imag_positive T z hz
  have hc : 0 < c := by dsimp [c]; positivity
  have hcz : c ≤ (G T z).im := by dsimp [c]; linarith
  have hlt : c < (G T z).im := by dsimp [c]; linarith
  have hlim : Tendsto (fun w => (G T w).im) (𝓝 z) (𝓝 (G T z).im) :=
    Complex.continuous_im.continuousAt.comp (h.spatial_differentiableAt T z hz).continuousAt
  have hmem : ∀ᶠ w in 𝓝 z, w ∈ survivingDomain γ T :=
    (isOpen_survivingDomain h.1 T).mem_nhds hz
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ survivingDomain γ T ∧ c < (G T w).im :=
    hmem.and (hlim.eventually (Ioi_mem_nhds hlt))
  simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 2 / (c * c))
  · filter_upwards [hnear] with w hw
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
      (h.pair_coefficient_intervalIntegrable hU T w z hw.1 hz)).aestronglyMeasurable
  · filter_upwards [hnear] with w hw
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
    exact h.pair_coefficient_bound T w z hw.1 hz c hc hw.2.le hcz u ⟨hu.1.le, hu.2⟩
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
    exact h.pair_coefficient_tendsto T z hz u hu.2

 

theorem loewner_spatial_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    deriv (G T) z = Complex.exp
      (∫ u in (0 : ℝ)..(T : ℝ), (-2 : ℂ) / (G u.toNNReal z - (U u.toNNReal : ℂ)) ^ 2) := by
  let L (w : ℂ) := Complex.exp (∫ u in (0 : ℝ)..(T : ℝ), loewnerPairCoefficient U G w z u)
  have hL : Tendsto L (𝓝 z) (𝓝 (L z)) :=
    Complex.continuous_exp.continuousAt.tendsto.comp (h.pair_integral_tendsto hU T z hz)
  have he : slope (G T) z =ᶠ[𝓝[≠] z] L := by
    have hnear : ∀ᶠ w in 𝓝 z, w ∈ survivingDomain γ T := (isOpen_survivingDomain h.1 T).mem_nhds hz
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwz
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr hwz
    rw [slope_def_field, h.difference_formula hU T w z hw hz]
    change (w - z) * L w / (w - z) = L w
    field_simp
  have hs : Tendsto (slope (G T) z) (𝓝[≠] z) (𝓝 (L z)) :=
    (hL.mono_left nhdsWithin_le_nhds).congr' he.symm
  have heq := tendsto_nhds_unique (h.spatial_differentiableAt T z hz).hasDerivAt.tendsto_slope hs
  simpa only [L, loewnerPairCoefficient, pow_two] using heq

 
noncomputable def fullRadius (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  2 * (G t z).im / ‖deriv (G t) z‖

lemma IsCapacityTwoWitness.derivative_norm_positive
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    0 < ‖deriv (G T) z‖ := by
  rw [loewner_spatial_derivative hU h T z hz, Complex.norm_exp]
  exact Real.exp_pos _

lemma IsCapacityTwoWitness.fullRadius_positive
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    0 < fullRadius G T z := by
  exact div_pos (mul_pos (by norm_num) (h.imag_positive T z hz))
    (h.derivative_norm_positive hU T z hz)

lemma IsCapacityTwoWitness.derivative_norm_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => ‖deriv (G v.toNNReal) z‖)
      (‖deriv (G u.toNNReal) z‖ * (loewnerPairCoefficient U G z z u).re)
      (Icc 0 (T : ℝ)) u := by
  let c := loewnerPairCoefficient U G z z
  let C (v : ℝ) : ℂ := c (projIcc 0 (T : ℝ) T.coe_nonneg v)
  have hc : ContinuousOn c (Icc 0 (T : ℝ)) := h.pair_coefficient_continuousOn hU T z z hz hz
  have hC : Continuous C := hc.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun v => (projIcc 0 (T : ℝ) T.coe_nonneg v).property)
  have hCc (v : ℝ) (hv : v ∈ Icc 0 (T : ℝ)) : C v = c v := by simp only [C, projIcc_of_mem T.coe_nonneg hv]
  let I (v : ℝ) : ℂ := ∫ t in (0 : ℝ)..v, C t
  have hI (v : ℝ) : HasDerivAt I (C v) v :=
    intervalIntegral.integral_hasDerivAt_right (hC.intervalIntegrable _ _)
      hC.aestronglyMeasurable.stronglyMeasurableAtFilter hC.continuousAt
  have heq (v : ℝ) (hv : v ∈ Icc 0 (T : ℝ)) :
      ‖deriv (G v.toNNReal) z‖ = Real.exp (I v).re := by
    rw [loewner_spatial_derivative hU h v.toNNReal z (h.live_at_real_time T z hz v hv.2), Complex.norm_exp]
    congr 2
    rw [Real.coe_toNNReal _ hv.1]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hv.1] at ht
    rw [hCc t ⟨ht.1, ht.2.trans hv.2⟩]
    simp only [c, loewnerPairCoefficient, pow_two]
  have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hI u)).exp.hasDerivWithinAt (s := Icc 0 (T : ℝ))
  have hh := hd.congr heq (heq u hu)
  simpa only [Function.comp_def, Complex.reCLM_apply, hCc u hu, ← heq u hu, c] using hh

lemma loewnerPairCoefficient_re (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ) :
    (loewnerPairCoefficient U G z z u).re =
      -2 * ((G u.toNNReal z - (U u.toNNReal : ℂ)).re ^ 2 - (G u.toNNReal z).im ^ 2) /
        Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ)) ^ 2 := by
  simp only [loewnerPairCoefficient, Complex.div_re, Complex.neg_re, Complex.re_ofNat,
    Complex.neg_im, Complex.im_ofNat, neg_zero, zero_mul, zero_div, add_zero,
    Complex.mul_re, Complex.normSq_mul, Complex.sub_im, Complex.ofReal_im, sub_zero,
    pow_two]

lemma IsCapacityTwoWitness.radius_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => fullRadius G v.toNNReal z)
      (-4 * (G u.toNNReal z).im ^ 2 /
        Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ)) ^ 2 * fullRadius G u.toNNReal z)
      (Icc 0 (T : ℝ)) u := by
  have hlu := h.live_at_real_time T z hz u hu.2
  have hJ := h.derivative_norm_positive hU u.toNNReal z hlu
  have hN : Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.mpr (h.centered_ne_zero _ z hlu)).ne'
  have hd := ((h.imag_derivative T z hz u hu).const_mul 2).div
    (h.derivative_norm_derivative hU T z hz u hu) hJ.ne'
  convert hd using 1
  try rfl
  rw [loewnerPairCoefficient_re]
  let X := (G u.toNNReal z - (U u.toNNReal : ℂ)).re
  let Y := (G u.toNNReal z).im
  let J := ‖deriv (G u.toNNReal) z‖
  let N := Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ))
  have hNeq : N = X ^ 2 + Y ^ 2 := by
    simp only [N, X, Y, Complex.normSq_apply, Complex.sub_im, Complex.ofReal_im, sub_zero, pow_two]
  change -4 * Y ^ 2 / N ^ 2 * (2 * Y / J) =
    ((2 * (-2 * Y / N)) * J - 2 * Y * (J * (-2 * (X ^ 2 - Y ^ 2) / N ^ 2))) / J ^ 2
  have hn : N ≠ 0 := hN
  have hj : J ≠ 0 := hJ.ne'
  field_simp
  rw [hNeq]
  ring

 
theorem loewner_radius_clock_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt
      (fun v : ℝ => Real.log ((2 * z.im) / fullRadius G v.toNNReal z))
      (4 * (G u.toNNReal z).im ^ 2 /
        (Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ))) ^ 2)
      (Icc 0 (T : ℝ)) u := by
  have hp := h.fullRadius_positive hU u.toNNReal z (h.live_at_real_time T z hz u hu.2)
  have hc : 2 * z.im ≠ 0 := ne_of_gt (mul_pos (by norm_num) hz.1.1)
  have hr := h.radius_derivative hU T z hz u hu
  have hd := ((hasDerivWithinAt_const u (Icc 0 (T : ℝ)) (2 * z.im)).div hr hp.ne').log
    (div_ne_zero hc hp.ne')
  convert hd using 1
  try rfl
  simp only [Pi.div_apply]
  field_simp [hp.ne', hc, (show z.im ≠ 0 from hz.1.1.ne')]
  ring

noncomputable def logLoewnerCoordinates (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ) : ℂ × ℝ :=
  (((G t.toNNReal z).re : ℂ) + (Real.log (G t.toNNReal z).im : ℂ) * Complex.I,
    Real.log ‖deriv (G t.toNNReal) z‖)

lemma IsCapacityTwoWitness.log_height_bounds
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    Real.log (G T z).im ≤ Real.log (G u.toNNReal z).im ∧
      Real.log (G u.toNNReal z).im ≤ Real.log z.im := by
  have hanti := h.imag_antitoneOn T z hz
  have hlow := hanti hu (show (T : ℝ) ∈ Icc 0 (T : ℝ) from ⟨T.coe_nonneg, le_rfl⟩) hu.2
  have hupp := hanti (show (0 : ℝ) ∈ Icc 0 (T : ℝ) from ⟨le_rfl, T.coe_nonneg⟩) hu hu.1
  simp only [Real.toNNReal_coe] at hlow
  simp only [Real.toNNReal_zero, h.initial_value z hz.1.1] at hupp
  exact ⟨Real.log_le_log (h.imag_positive T z hz) hlow,
    Real.log_le_log (h.imag_positive _ z (h.live_at_real_time T z hz u hu.2)) hupp⟩

lemma clippedCenter_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (lo hi : ℝ) (hle : lo ≤ hi)
    (hlo : lo ≤ Real.log (G T z).im) (hhi : Real.log z.im ≤ hi)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    clippedCenter lo hi hle (U u.toNNReal) (logLoewnerCoordinates G z u) =
      G u.toNNReal z - (U u.toNNReal : ℂ) := by
  obtain ⟨ha, hb⟩ := h.log_height_bounds T z hz u hu
  have hmem : Real.log (G u.toNNReal z).im ∈ Icc lo hi := ⟨hlo.trans ha, hb.trans hhi⟩
  have him := h.imag_positive _ z (h.live_at_real_time T z hz u hu.2)
  simp only [clippedCenter, clippedHeight, logLoewnerCoordinates, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    mul_one, zero_add, projIcc_of_mem hle hmem, Real.exp_log him]
  apply Complex.ext <;> simp

lemma logLoewnerCoordinates_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (lo hi : ℝ) (hle : lo ≤ hi)
    (hlo : lo ≤ Real.log (G T z).im) (hhi : Real.log z.im ≤ hi)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (logLoewnerCoordinates G z)
      (clippedLogLoewnerField lo hi hle (U u.toNNReal) (logLoewnerCoordinates G z u))
      (Icc 0 (T : ℝ)) u := by
  have hzlive := h.live_at_real_time T z hz u hu.2
  have hy := h.imag_positive _ z hzlive
  have hj := h.derivative_norm_positive hU _ z hzlive
  have hdre := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt u (h.time_derivative T z hz u hu)
  have hdY := (h.imag_derivative T z hz u hu).log hy.ne'
  have hdJ := (h.derivative_norm_derivative hU T z hz u hu).log hj.ne'
  have hd := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt u hdre).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt u hdY).mul_const Complex.I)).prodMk hdJ
  convert hd using 1 <;> try rfl
  unfold clippedLogLoewnerField
  rw [clippedCenter_logCoordinates h T z hz lo hi hle hlo hhi u hu]
  dsimp only [Function.comp_def, Complex.reCLM_apply, Complex.ofRealCLM_apply]
  apply Prod.ext
  · apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero,
        div_eq_mul_inv, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
        zero_mul, sub_zero]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
        Complex.normSq_inv]
      field_simp [hy.ne']
  · change (-2 * (G u.toNNReal z - (U u.toNNReal : ℂ))⁻¹ ^ 2).re =
      (_ * (loewnerPairCoefficient U G z z u).re) / _
    rw [mul_div_cancel_left₀ _ hj.ne']
    congr 1
    simp only [loewnerPairCoefficient, div_eq_mul_inv, mul_inv_rev, pow_two]

lemma hasDerivWithinAt_Ici_of_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {a b u : ℝ} (hu : u ∈ Ico a b)
    (hf : HasDerivWithinAt f f' (Icc a b) u) : HasDerivWithinAt f f' (Ici u) u := by
  apply hf.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hu.2)] with x hx hxT
  exact ⟨hu.1.trans hx, hxT⟩

lemma logLoewnerCoordinates_initial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (hz : z ∈ survivingDomain γ 0) :
    logLoewnerCoordinates G z 0 = ((z.re : ℂ) + (Real.log z.im : ℂ) * Complex.I, 0) := by
  simp only [logLoewnerCoordinates, Real.toNNReal_zero, h.initial_value z hz.1.1,
    loewner_spatial_derivative hU h 0 z hz, NNReal.coe_zero,
    intervalIntegral.integral_same, Complex.exp_zero, norm_one, Real.log_one]

 

theorem clipped_log_loewner_agrees
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (lo hi : ℝ) (hle : lo ≤ hi)
    (hlo : lo ≤ Real.log (G T z).im) (hhi : Real.log z.im ≤ hi)
    (Q : ℝ → ℂ × ℝ)
    (hQ0 : Q 0 = ((z.re : ℂ) + (Real.log z.im : ℂ) * Complex.I, 0))
    (hQ : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) (Icc 0 (T : ℝ)) t) :
    EqOn Q (logLoewnerCoordinates G z) (Icc 0 (T : ℝ)) := by
  obtain ⟨L, K, hb, hl⟩ := clippedLogLoewnerField_bounds lo hi hle
  have hd := logLoewnerCoordinates_derivative hU h T z hz lo hi hle hlo hhi
  apply ODE_solution_unique (fun t => hl (U t.toNNReal))
    (fun t ht => (hQ t ht).continuousWithinAt)
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hQ t ⟨ht.1, ht.2.le⟩))
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hd t ⟨ht.1, ht.2.le⟩))
  exact hQ0.trans (logLoewnerCoordinates_initial hU h z (survivingDomain_antitone γ bot_le hz)).symm

 

theorem loewner_survival_of_positive_solution
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (W : ℝ → ℂ)
    (hWp : ∀ u ∈ Icc 0 (T : ℝ), 0 < (W u).im)
    (hWd : ∀ u ∈ Icc 0 (T : ℝ), HasDerivWithinAt W
      (2 / (W u - (U u.toNNReal : ℂ))) (Icc 0 (T : ℝ)) u) :
    W 0 ∈ survivingDomain γ T ∧ G T (W 0) = W T := by
  let w := F T (W T)
  have hWT : W T ∈ upperHalfPlane := hWp T ⟨T.coe_nonneg, le_rfl⟩
  have hw : w ∈ survivingDomain γ T := h.2.2.2.2.2.2.1 T hWT
  have hGw : G T w = W T := h.2.2.2.2.2.2.2.2.1 T (W T) hWT
  have hWc : ContinuousOn W (Icc 0 (T : ℝ)) := fun u hu => (hWd u hu).continuousWithinAt
  have hWnz (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) : W u - (U u.toNNReal : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hh
    exact (hWp u hu).ne' hh
  let c (u : ℝ) : ℂ := (-2 : ℂ) /
    ((G u.toNNReal w - (U u.toNNReal : ℂ)) * (W u - (U u.toNNReal : ℂ)))
  have hUc : Continuous (fun u : ℝ => (U u.toNNReal : ℂ)) :=
    Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)
  have hc : ContinuousOn c (Icc 0 (T : ℝ)) :=
    continuousOn_const.div
      (((h.time_continuousOn T w hw).sub hUc.continuousOn).mul (hWc.sub hUc.continuousOn))
      (fun u hu => mul_ne_zero (h.centered_ne_zero _ w (h.live_at_real_time T w hw u hu.2)) (hWnz u hu))
  have hd (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
      HasDerivWithinAt (fun s : ℝ => G s.toNNReal w - W s)
        (c u * (G u.toNNReal w - W u)) (Icc 0 (T : ℝ)) u := by
    have hg := h.centered_ne_zero _ w (h.live_at_real_time T w hw u hu.2)
    have hn := hWnz u hu
    have he : c u * (G u.toNNReal w - W u) =
        2 / (G u.toNNReal w - (U u.toNNReal : ℂ)) - 2 / (W u - (U u.toNNReal : ℂ)) := by
      dsimp only [c]
      field_simp
      ring
    rw [he]
    exact (h.time_derivative T w hw u hu).sub (hWd u hu)
  have he := complex_linear_ode_exp (T : ℝ) T.coe_nonneg
    (fun s : ℝ => G s.toNNReal w - W s) c hc hd
  simp only [Real.toNNReal_coe, hGw, sub_self, Real.toNNReal_zero,
    h.initial_value w hw.1.1] at he
  have hw0 : w = W 0 := sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right (Complex.exp_ne_zero _))
  exact ⟨hw0 ▸ hw, hw0 ▸ hGw⟩

end SLEExactGauge
end

 
end

end OAI

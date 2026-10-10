import OAI.Probability.FreeIsing.Energy.Attenuation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianVarianceLower

private lemma tanh_strictMono : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_tanh_response x).deriv]
  exact sub_pos.mpr (Real.tanh_sq_lt_one x)

private lemma tanh_abs (x : ℝ) : Real.tanh |x| = |Real.tanh x| := by
  rcases le_total 0 x with hx | hx
  · have ht : 0 ≤ Real.tanh x := by
      simpa only [Real.tanh_zero] using tanh_strictMono.monotone hx
    rw [abs_of_nonneg hx, abs_of_nonneg ht]
  · have ht : Real.tanh x ≤ 0 := by
      simpa only [Real.tanh_zero] using tanh_strictMono.monotone hx
    rw [abs_of_nonpos hx, Real.tanh_neg, abs_of_nonpos ht]

def varianceLower (T K : ℝ) : ℝ :=
  (1 - Real.tanh (T + 1 + K) ^ 2) ^ 2 / 2

lemma varianceLower_pos (T K : ℝ) : 0 < varianceLower T K := by
  unfold varianceLower
  exact div_pos (sq_pos_of_pos (sub_pos.mpr (Real.tanh_sq_lt_one _))) (by norm_num)

lemma squared_variance_le_one (x : ℝ) : (1 - Real.tanh x ^ 2) ^ 2 ≤ 1 := by
  have := Real.tanh_sq_lt_one x
  have := sq_nonneg (Real.tanh x)
  nlinarith

lemma squared_variance_lower_on_abs_le {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) :
    (1 - Real.tanh R ^ 2) ^ 2 ≤ (1 - Real.tanh x ^ 2) ^ 2 := by
  have ht0 : 0 ≤ Real.tanh R := by
    simpa only [Real.tanh_zero] using tanh_strictMono.monotone hR
  have ht : |Real.tanh x| ≤ Real.tanh R := by
    rw [← tanh_abs]
    exact tanh_strictMono.monotone hx
  have hsq : Real.tanh x ^ 2 ≤ Real.tanh R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ht0).mpr ht
  nlinarith [Real.tanh_sq_lt_one x, Real.tanh_sq_lt_one R]

lemma integrable_squared_variance {h : ℝ → ℝ} (hh : Measurable h) (v : ℝ≥0) :
    Integrable (fun z => (1 - Real.tanh (h z) ^ 2) ^ 2) (gaussianReal 0 v) := by
  have hm : Measurable (fun z => (1 - Real.tanh (h z) ^ 2) ^ 2) := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact squared_variance_le_one (h z)

theorem varianceLower_le_integral {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    {v : ℝ≥0} (hv : (v : ℝ) ≤ T) {h : ℝ → ℝ} (hh : Measurable h)
    (hshift : ∀ z, |h z - z| ≤ K) :
    varianceLower T K ≤ ∫ z, (1 - Real.tanh (h z) ^ 2) ^ 2 ∂gaussianReal 0 v := by
  let R := T + 1
  let c := (1 - Real.tanh (R + K) ^ 2) ^ 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hc : 0 ≤ c := sq_nonneg _
  have hpoint (z : ℝ) : c * (1 - z ^ 2 / R ^ 2) ≤
      (1 - Real.tanh (h z) ^ 2) ^ 2 := by
    by_cases hz : |z| ≤ R
    · have hhbound : |h z| ≤ R + K := by
        calc
          |h z| = |z + (h z - z)| := by congr 1; ring
          _ ≤ |z| + |h z - z| := abs_add_le _ _
          _ ≤ R + K := add_le_add hz (hshift z)
      have hlow := squared_variance_lower_on_abs_le (by linarith : 0 ≤ R + K) hhbound
      have hdiv : 0 ≤ z ^ 2 / R ^ 2 := div_nonneg (sq_nonneg _) hR2.le
      have hprod := mul_nonneg hc hdiv
      dsimp [c] at *
      nlinarith
    · have hsq : R ^ 2 ≤ z ^ 2 := by
        have hle : R ≤ |z| := le_of_lt (lt_of_not_ge hz)
        simpa only [sq_abs] using (sq_le_sq₀ hR.le (abs_nonneg z)).mpr hle
      have hdiv : 1 ≤ z ^ 2 / R ^ 2 := (le_div_iff₀ hR2).2 (by simpa using hsq)
      have hprod := mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hdiv)
      exact hprod.trans (sq_nonneg _)
  have hsquare : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
    simpa only [id_eq] using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hmoment : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
    have hvar := variance_fun_id_gaussianReal (μ := 0) (v := v)
    rw [variance_eq_integral (X := fun z : ℝ => z) measurable_id'.aemeasurable] at hvar
    simpa only [integral_id_gaussianReal, sub_zero] using hvar
  have hpoly : Integrable (fun z : ℝ => c * (1 - z ^ 2 / R ^ 2))
      (gaussianReal 0 v) :=
    ((integrable_const (1 : ℝ)).sub (hsquare.div_const (R ^ 2))).const_mul c
  have hint := integral_mono hpoly (integrable_squared_variance hh v) hpoint
  have heval : (∫ z : ℝ, c * (1 - z ^ 2 / R ^ 2) ∂gaussianReal 0 v) =
      c * (1 - (v : ℝ) / R ^ 2) := by
    rw [integral_const_mul, integral_sub (integrable_const _) (hsquare.div_const _),
      integral_div, hmoment]
    simp
  rw [heval] at hint
  have hratio : (v : ℝ) / R ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ hR2).2
    dsimp [R]
    nlinarith [sq_nonneg T]
  have hprod := mul_le_mul_of_nonneg_left hratio hc
  change c / 2 ≤ _
  nlinarith

theorem varianceLower_mul_integral_le
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {h : ℝ × Y → ℝ} {weight : Y → ℝ}
    (hh : Measurable h) (hw : Measurable weight) (hint : Integrable weight ν)
    (hnonneg : ∀ y, 0 ≤ weight y)
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) {v : ℝ≥0} (hv : (v : ℝ) ≤ T)
    (hshift : ∀ z y, |h (z, y) - z| ≤ K) :
    varianceLower T K * (∫ y, weight y ∂ν) ≤
      ∫ p : ℝ × Y, (1 - Real.tanh (h p) ^ 2) ^ 2 * weight p.2
        ∂(gaussianReal 0 v).prod ν := by
  let F : ℝ × Y → ℝ := fun p => (1 - Real.tanh (h p) ^ 2) ^ 2 * weight p.2
  have hm : Measurable F := by
    dsimp [F]
    simp only [Real.tanh_eq_sinh_div_cosh]
    fun_prop
  have hF : Integrable F ((gaussianReal 0 v).prod ν) := by
    apply (hint.comp_snd (gaussianReal 0 v)).mono' hm.aestronglyMeasurable
    refine Filter.Eventually.of_forall fun p => ?_
    change ‖(1 - Real.tanh (h p) ^ 2) ^ 2 * weight p.2‖ ≤ weight p.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hnonneg p.2))]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (squared_variance_le_one (h p)) (hnonneg p.2)
  have hbound (y : Y) : varianceLower T K * weight y ≤
      ∫ z, F (z, y) ∂gaussianReal 0 v := by
    have hslice : Measurable (fun z : ℝ => h (z, y)) :=
      hh.comp (measurable_id.prodMk measurable_const)
    have hlower := varianceLower_le_integral hT hK hv hslice (fun z => hshift z y)
    change varianceLower T K * weight y ≤
      ∫ z, (1 - Real.tanh (h (z, y)) ^ 2) ^ 2 * weight y ∂gaussianReal 0 v
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right hlower (hnonneg y)
  change varianceLower T K * (∫ y, weight y ∂ν) ≤ ∫ p, F p ∂(gaussianReal 0 v).prod ν
  rw [integral_prod_symm F hF, ← integral_const_mul]
  exact integral_mono (hint.const_mul _) hF.integral_prod_right hbound

theorem varianceLower_mul_integral_le_of_indepFun
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → ℝ} {Z : Ω → Y}
    {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    (hZ : AEMeasurable Z P) (hind : IndepFun X Z P)
    {h : ℝ × Y → ℝ} {weight : Y → ℝ}
    (hh : Measurable h) (hw : Measurable weight)
    (hint : Integrable (fun ω => weight (Z ω)) P) (hnonneg : ∀ y, 0 ≤ weight y)
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) (hv : (v : ℝ) ≤ T)
    (hshift : ∀ z y, |h (z, y) - z| ≤ K) :
    varianceLower T K * (∫ ω, weight (Z ω) ∂P) ≤
      ∫ ω, (1 - Real.tanh (h (X ω, Z ω)) ^ 2) ^ 2 * weight (Z ω) ∂P := by
  let F : ℝ × Y → ℝ := fun p => (1 - Real.tanh (h p) ^ 2) ^ 2 * weight p.2
  have hm : Measurable F := by
    dsimp [F]
    simp only [Real.tanh_eq_sinh_div_cosh]
    fun_prop
  have hpair : HasLaw (fun ω => (X ω, Z ω)) ((gaussianReal 0 v).prod (P.map Z)) P := by
    refine ⟨hX.aemeasurable.prodMk hZ, ?_⟩
    rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hZ, hX.map_eq]
  have hwInt : Integrable weight (P.map Z) :=
    (integrable_map_measure hw.aestronglyMeasurable hZ).2 hint
  have hlower := varianceLower_mul_integral_le (P.map Z) hh hw hwInt hnonneg hT hK hv hshift
  rw [integral_map hZ hw.aestronglyMeasurable] at hlower
  calc
    _ ≤ ∫ p, F p ∂(gaussianReal 0 v).prod (P.map Z) := hlower
    _ = _ := (hpair.integral_comp hm.aestronglyMeasurable).symm

theorem integrable_weight_of_integrable_weighted_variance
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {h : ℝ × Y → ℝ} {weight : Y → ℝ}
    (hh : Measurable h) (hw : Measurable weight) (hnonneg : ∀ y, 0 ≤ weight y)
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) {v : ℝ≥0} (hv : (v : ℝ) ≤ T)
    (hshift : ∀ z y, |h (z, y) - z| ≤ K)
    (hraw : Integrable (fun p : ℝ × Y =>
      (1 - Real.tanh (h p) ^ 2) ^ 2 * weight p.2) ((gaussianReal 0 v).prod ν)) :
    Integrable weight ν := by
  have hbound (y : Y) : varianceLower T K * weight y ≤
      ∫ z, (1 - Real.tanh (h (z, y)) ^ 2) ^ 2 * weight y ∂gaussianReal 0 v := by
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right
      (varianceLower_le_integral hT hK hv
        (hh.comp (measurable_id.prodMk measurable_const)) (fun z => hshift z y))
      (hnonneg y)
  apply (hraw.integral_prod_right.div_const (varianceLower T K)).mono'
    hw.aestronglyMeasurable
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg y)]
  apply (le_div_iff₀ (varianceLower_pos T K)).2
  simpa only [mul_comm] using hbound y

theorem integral_weight_le_of_integrable_weighted_variance
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {h : ℝ × Y → ℝ} {weight : Y → ℝ}
    (hh : Measurable h) (hw : Measurable weight) (hnonneg : ∀ y, 0 ≤ weight y)
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) {v : ℝ≥0} (hv : (v : ℝ) ≤ T)
    (hshift : ∀ z y, |h (z, y) - z| ≤ K)
    (hraw : Integrable (fun p : ℝ × Y =>
      (1 - Real.tanh (h p) ^ 2) ^ 2 * weight p.2) ((gaussianReal 0 v).prod ν)) :
    Integrable weight ν ∧ (∫ y, weight y ∂ν) ≤
      (∫ p : ℝ × Y, (1 - Real.tanh (h p) ^ 2) ^ 2 * weight p.2
        ∂(gaussianReal 0 v).prod ν) / varianceLower T K := by
  have hint := integrable_weight_of_integrable_weighted_variance ν hh hw hnonneg hT hK hv
    hshift hraw
  refine ⟨hint, (le_div_iff₀ (varianceLower_pos T K)).2 ?_⟩
  simpa only [mul_comm] using
    varianceLower_mul_integral_le ν hh hw hint hnonneg hT hK hv hshift

end Problem367.GaussianVarianceLower

end

end OAI

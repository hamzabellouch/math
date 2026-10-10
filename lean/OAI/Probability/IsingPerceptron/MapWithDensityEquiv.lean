import Mathlib
import OAI.Probability.IsingPerceptron.PoissonCloud

namespace OAI

/-! Map With Density Equiv. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (e : E ≃ᵐ F) (μ : Measure E) {w : E → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (w ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    _ = ∫⁻ x, w x * f (e x) ∂μ := by
      rw [lintegral_map hf e.measurable]
      exact lintegral_withDensity_eq_lintegral_mul μ hw
        (show Measurable (fun x => f (e x)) from hf.comp e.measurable)
    _ = ∫⁻ x, (w (e.symm x) * f x) ∂μ.map e := by
      simpa only [Pi.mul_apply, Function.comp_apply, e.symm_apply_apply] using
        (lintegral_map (μ := μ) ((hw.comp e.symm.measurable).mul hf) e.measurable).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _
      (hw.comp e.symm.measurable) hf).symm

def powerIntensityDensity (b : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (if 0 < x then b * x ^ (-1-b) else 0)

def powerIntensity (b : ℝ) : Measure ℝ := volume.withDensity (powerIntensityDensity b)

lemma measurable_powerIntensityDensity (b : ℝ) : Measurable (powerIntensityDensity b) := by
  unfold powerIntensityDensity
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · fun_prop
  · fun_prop

lemma powerIntensityDensity_scale {b c : ℝ} (hc : 0 < c) (x : ℝ) :
    ENNReal.ofReal c⁻¹ * powerIntensityDensity b (c⁻¹ * x) =
      ENNReal.ofReal (c ^ b) * powerIntensityDensity b x := by
  have hpos : 0 < c⁻¹ * x ↔ 0 < x := mul_pos_iff_of_pos_left (inv_pos.mpr hc)
  unfold powerIntensityDensity
  by_cases hx : 0 < x
  · simp only [ite_eq_left hx, ite_eq_left (hpos.mpr hx)]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le b)]
    congr 1
    rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hx.le,
      Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
    have he : c⁻¹ * c ^ (-(-1-b)) = c ^ b := by
      rw [show -(-1-b) = b + 1 by ring, Real.rpow_add hc]
      simp only [Real.rpow_one]
      field_simp
    calc
       c⁻¹ * (b * (c ^ (-(-1-b)) * x ^ (-1-b))) =
           b * (c⁻¹ * c ^ (-(-1-b))) * x ^ (-1-b) := by ring
       _ = c ^ b * (b * x ^ (-1-b)) := by rw [he]; ring
  · simp only [ite_eq_right hx, ite_eq_right (fun h => hx (hpos.mp h)), ENNReal.ofReal_zero,
      mul_zero]

theorem map_powerIntensity_mul {b c : ℝ} (hc : 0 < c) :
    (powerIntensity b).map (fun x => c*x) =
      ENNReal.ofReal (c ^ b) • powerIntensity b := by
  let e := MeasurableEquiv.mulLeft₀ c hc.ne'
  have hm := map_withDensity_equiv e volume (measurable_powerIntensityDensity b)
  change (volume.withDensity (powerIntensityDensity b)).map e = _
  rw [hm]
  change (volume.map (fun x => c*x)).withDensity
    (fun x => powerIntensityDensity b (c⁻¹*x)) = _
  unfold powerIntensity
  rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc),
    withDensity_smul_measure, ← withDensity_smul (ENNReal.ofReal c⁻¹)
      (show Measurable (fun x => powerIntensityDensity b (c⁻¹*x)) from
        (measurable_powerIntensityDensity b).comp (measurable_const_mul c⁻¹)),
    ← withDensity_smul (ENNReal.ofReal (c^b)) (measurable_powerIntensityDensity b)]
  congr 1
  funext x
  exact powerIntensityDensity_scale hc x

instance powerIntensity_sigmaFinite (b : ℝ) : SigmaFinite (powerIntensity b) := by
  unfold powerIntensity powerIntensityDensity
  infer_instance

theorem map_marked_powerIntensity {E : Type*} [MeasurableSpace E]
    (b : ℝ) (μ : Measure E) [SFinite μ] {a : E → ℝ}
    (ha : Measurable a) (hpos : ∀ y, 0 < a y) :
    ((powerIntensity b).prod μ).map (fun p : ℝ × E => (a p.2 * p.1, p.2)) =
      (powerIntensity b).prod (μ.withDensity (fun y => ENNReal.ofReal (a y ^ b))) := by
  have hw : Measurable (fun y => ENNReal.ofReal (a y ^ b)) := by fun_prop
  have hT : Measurable (fun p : ℝ × E => (a p.2 * p.1, p.2)) := by fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    _ = ∫⁻ y, ∫⁻ x, f (a y*x,y) ∂powerIntensity b ∂μ := by
      rw [lintegral_map hf hT]
      exact lintegral_prod_symm _ (hf.comp hT).aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (a y ^ b) *
        (∫⁻ x, f (x,y) ∂powerIntensity b) ∂μ := by
      apply lintegral_congr
      intro y
      have hy : Measurable (fun x : ℝ => f (x,y)) := hf.comp (measurable_id.prodMk measurable_const)
      rw [← lintegral_map hy (measurable_const_mul (a y)), map_powerIntensity_mul (hpos y),
        lintegral_smul_measure]
      rfl
    _ = ∫⁻ y, ∫⁻ x, f (x,y) ∂powerIntensity b
        ∂μ.withDensity (fun y => ENNReal.ofReal (a y ^ b)) := by
      exact (lintegral_withDensity_eq_lintegral_mul μ hw hf.lintegral_prod_left').symm
    _ = _ := (lintegral_prod_symm f hf.aemeasurable).symm

lemma poissonLaw_congr {E : Type*} [MeasurableSpace E] [Nonempty E]
    {μ ν : Measure E} [SFinite μ] [SFinite ν] (h : μ = ν) : poissonLaw μ = poissonLaw ν := by
  subst ν
  rfl

theorem poissonLaw_marked_power {E : Type*} [MeasurableSpace E] [Nonempty E]
    (b : ℝ) (μ : Measure E) [SFinite μ] {a : E → ℝ}
    (ha : Measurable a) (hpos : ∀ y, 0 < a y) :
    (poissonLaw ((powerIntensity b).prod μ)).map
      (fun ν => ν.map (fun p : ℝ × E => (a p.2 * p.1, p.2))) =
    poissonLaw ((powerIntensity b).prod (μ.withDensity (fun y => ENNReal.ofReal (a y ^ b)))) := by
  have hT : Measurable (fun p : ℝ × E => (a p.2 * p.1, p.2)) := by fun_prop
  exact (poissonLaw_map _ hT).trans
    (poissonLaw_congr (map_marked_powerIntensity b μ ha hpos))

open Set

lemma integrable_power_min {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable (fun x : ℝ => min 1 (max x 0)) (powerIntensity b) := by
  rw [powerIntensity, integrable_withDensity_iff (measurable_powerIntensityDensity b)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi : IntegrableOn (fun x : ℝ => x ^ (-b)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have hj : IntegrableOn (fun x : ℝ => x ^ (-1-b)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have H₁ : Integrable ((Ioc (0:ℝ) 1).indicator (fun x => b * x ^ (-b))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (hi.const_mul b)
  have H₂ : Integrable ((Ioi (1:ℝ)).indicator (fun x => b * x ^ (-1-b))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hj.const_mul b)
  have H := H₁.add H₂
  apply H.congr
  apply ae_of_all
  intro x
  symm
  simp only [Pi.add_apply]
  by_cases hx : 0 < x
  · simp only [powerIntensityDensity, ite_eq_left hx,
      ENNReal.toReal_ofReal (mul_nonneg hb.le (Real.rpow_nonneg hx.le _)), max_eq_left hx.le]
    by_cases hx1 : x ≤ 1
    · rw [min_eq_right hx1, indicator_of_mem (show x ∈ Ioc (0:ℝ) 1 from ⟨hx,hx1⟩),
        indicator_of_notMem (show x ∉ Ioi (1:ℝ) from not_lt.mpr hx1), add_zero]
      have hp : x * x ^ (-1-b) = x ^ (-b) := by
        calc
          x * x ^ (-1-b) = x ^ (1 + (-1-b)) := by rw [Real.rpow_add hx, Real.rpow_one]
          _ = x ^ (-b) := by congr 1; ring
      nlinarith [hp]
    · rw [min_eq_left (le_of_lt (lt_of_not_ge hx1)), one_mul,
        indicator_of_notMem (show x ∉ Ioc (0:ℝ) 1 from fun h => hx1 h.2),
        indicator_of_mem (show x ∈ Ioi (1:ℝ) from lt_of_not_ge hx1), zero_add]
  · simp [powerIntensityDensity, hx, max_eq_right (le_of_not_gt hx),
      indicator_of_notMem (show x ∉ Ioi (1:ℝ) from fun h => hx (lt_trans zero_lt_one h))]

def stableLaplaceCost (x : ℝ) : ℝ := 1 - Real.exp (-max x 0)

def stableLaplaceConstant (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (stableLaplaceCost x) ∂powerIntensity b

lemma measurable_stableLaplaceCost : Measurable stableLaplaceCost := by
  unfold stableLaplaceCost
  fun_prop

lemma stableLaplaceCost_nonneg (x : ℝ) : 0 ≤ stableLaplaceCost x := by
  unfold stableLaplaceCost
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _)))

lemma stableLaplaceCost_le_min (x : ℝ) : stableLaplaceCost x ≤ min 1 (max x 0) := by
  unfold stableLaplaceCost
  exact le_min (by linarith [Real.exp_pos (-max x 0)])
    (by linarith [Real.add_one_le_exp (-max x 0)])

lemma integrable_stableLaplaceCost {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable stableLaplaceCost (powerIntensity b) := by
  apply (integrable_power_min hb hb1).mono' measurable_stableLaplaceCost.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (stableLaplaceCost_nonneg x)]
    exact stableLaplaceCost_le_min x

lemma stableLaplaceConstant_lt_top {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b < ∞ := by
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ stableLaplaceCost_nonneg)).mp
    (integrable_stableLaplaceCost hb hb1).hasFiniteIntegral

lemma stableLaplaceConstant_pos {b : ℝ} (hb : 0 < b) : 0 < stableLaplaceConstant b := by
  unfold stableLaplaceConstant powerIntensity
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_powerIntensityDensity b)
    measurable_stableLaplaceCost.ennreal_ofReal]
  apply (lintegral_pos_iff_support ((measurable_powerIntensityDensity b).mul
    measurable_stableLaplaceCost.ennreal_ofReal)).mpr
  have hs : Function.support (powerIntensityDensity b * (fun x => ENNReal.ofReal (stableLaplaceCost x))) =
      Ioi (0:ℝ) := by
    ext x
    by_cases hx : 0 < x
    · have hp : 0 < b * x ^ (-1-b) := mul_pos hb (Real.rpow_pos_of_pos hx _)
      have hc : 0 < 1 - Real.exp (-x) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
      simp [Function.mem_support, powerIntensityDensity, stableLaplaceCost, hx,
        max_eq_left hx.le, ne_of_gt (ENNReal.ofReal_pos.mpr hp), ne_of_gt (ENNReal.ofReal_pos.mpr hc)]
    · simp [Function.mem_support, powerIntensityDensity, hx]
  rw [hs]
  simp

end IsingPerceptron

namespace IsingPerceptron

lemma integrable_negExp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) : Integrable (fun ω => negExp (X ω)) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_negExp.measurable.comp hX).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change ‖negExp (X ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]
    exact negExp_le_one _

lemma measure_zero_of_integral_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : ℕ → Ω → ℝ} (hfi : ∀ n, Integrable (f n) P)
    (hfpos : ∀ n ω, 0 ≤ f n ω) (hb : ∀ n ω, ω ∈ A → 1 ≤ f n ω)
    (ht : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 0)) : P A = 0 := by
  apply (measureReal_eq_zero_iff (μ := P) (s := A)).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto' ht
  intro n
  rw [← integral_indicator_one hA]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hA) (hfi n)
  intro ω
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω, Pi.one_apply] using hb n ω hω
  · simpa only [indicator_of_notMem hω] using hfpos n ω

theorem stable_laplace_finite_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) {C b : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hl : ∀ t : ℝ, 0 < t →
      (∫ ω, negExp (ENNReal.ofReal t * X ω) ∂P) = Real.exp (-C * t ^ b)) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  have hi (t : ℝ) : Integrable (fun ω => negExp (ENNReal.ofReal t * X ω)) P :=
    integrable_negExp P (measurable_const.mul hX)
  have hfinite : P {ω | X ω = ∞} = 0 := by
    let t : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
    have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton ∞))
      (f := fun n ω => 1 - negExp (ENNReal.ofReal (t n) * X ω))
    · intro n
      exact (integrable_const 1).sub (hi (t n))
    · intro n ω
      exact sub_nonneg.mpr (negExp_le_one _)
    · intro n ω hω
      change X ω = ∞ at hω
      simp [hω, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (htpos n)))]
    · have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hr : Tendsto (fun n => (t n)^b) atTop (𝓝 0) := by
        simpa only [Function.comp_def, Real.zero_rpow hb.ne'] using (Real.continuous_rpow_const hb.le).continuousAt.tendsto.comp ht
      have he : Tendsto (fun n => 1 - Real.exp (-C * (t n)^b)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, mul_zero, Real.exp_zero, sub_self] using
          (tendsto_const_nhds (x := (1:ℝ))).sub (Real.continuous_exp.continuousAt.tendsto.comp (hr.const_mul (-C)))
      convert he using 1
      ext n
      rw [integral_sub (integrable_const 1) (hi (t n)), hl _ (htpos n), integral_const]
      simp
  have hpositive : P {ω | X ω = 0} = 0 := by
    let t : ℕ → ℝ := fun n => (n:ℝ)+1
    have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton 0))
      (f := fun n ω => negExp (ENNReal.ofReal (t n) * X ω))
    · exact fun n => hi (t n)
    · exact fun _ _ => negExp_nonneg _
    · intro n ω hω
      change X ω = 0 at hω
      simp [hω]
    · have ht : Tendsto t atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      have hr := (tendsto_rpow_atTop hb).comp ht
      have he := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hC hr))
      simpa only [hl _ (htpos _), Function.comp_def, neg_mul] using he
  have hf : ∀ᵐ ω ∂P, X ω ≠ ∞ := by simpa only [ae_iff, not_not] using hfinite
  have hp : ∀ᵐ ω ∂P, X ω ≠ 0 := by simpa only [ae_iff, not_not] using hpositive
  filter_upwards [hf, hp] with ω hf hp
  exact ⟨pos_iff_ne_zero.mpr hp, lt_top_iff_ne_top.mpr hf⟩

def poissonTotal (ν : Measure ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (max x 0) ∂ν

lemma measurable_poissonTotal : Measurable poissonTotal :=
  Measure.measurable_lintegral (by fun_prop)

lemma stableLaplaceCost_scale (t x : ℝ) (ht : 0 ≤ t) :
    stableLaplaceCost (t*x) = 1-Real.exp (-t * max x 0) := by
  have hm : max (t*x) 0 = t * max x 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg x 0 ht).symm
  rw [stableLaplaceCost, hm]
  congr 2
  ring

lemma powerIntensity_laplace_scale {b t : ℝ} (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (1-Real.exp (-t * max x 0)) ∂powerIntensity b) =
    ENNReal.ofReal (t^b) * stableLaplaceConstant b := by
  simp_rw [← stableLaplaceCost_scale t _ ht.le]
  rw [← lintegral_map measurable_stableLaplaceCost.ennreal_ofReal
    (measurable_const_mul t), map_powerIntensity_mul ht, lintegral_smul_measure]
  rfl

theorem poissonTotal_laplace (b : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ ν, negExp (ENNReal.ofReal t * poissonTotal ν) ∂poissonLaw (powerIntensity b)) =
    negExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b) := by
  have hm : Measurable (fun x : ℝ => t * max x 0) := by fun_prop
  have h := poissonLaw_laplace (powerIntensity b) hm (fun x => mul_nonneg ht.le (le_max_right _ _))
  simpa only [ENNReal.ofReal_mul ht.le, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    poissonTotal, ← neg_mul, powerIntensity_laplace_scale ht] using h

theorem poissonTotal_finite_positive {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∀ᵐ ν ∂poissonLaw (powerIntensity b), 0 < poissonTotal ν ∧ poissonTotal ν < ∞ := by
  have hfin := stableLaplaceConstant_lt_top hb hb1
  have hpos := stableLaplaceConstant_pos hb
  apply stable_laplace_finite_positive _ measurable_poissonTotal
    (ENNReal.toReal_pos hpos.ne' hfin.ne) hb
  intro t ht
  rw [poissonTotal_laplace b ht, ← ENNReal.ofReal_toReal hfin.ne,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), negExp_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  congr 1
  ring

lemma integrable_exp_neg_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (-t * X ω)) P := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hpos] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hω)

lemma measureReal_mul_le_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : Ω → ℝ} (hf : Integrable f P) (hfpos : 0 ≤ᵐ[P] f) (c : ℝ)
    (hc : ∀ᵐ ω ∂P, ω ∈ A → c ≤ f ω) : P.real A * c ≤ ∫ ω, f ω ∂P := by
  rw [← smul_eq_mul, ← integral_indicator_const c hA]
  apply integral_mono_ae ((integrable_const c).indicator hA) hf
  filter_upwards [hfpos, hc] with ω hp hb
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω] using hb hω
  · simpa only [indicator_of_notMem hω, Pi.zero_apply] using hp

lemma stable_laplace_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < X ω} ≤ ENNReal.ofReal (C / (1-Real.exp (-1)) * s^(-b)) := by
  have hc : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hi := integrable_exp_neg_mul P hX hpos (inv_nonneg.mpr hs.le)
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX)
    ((integrable_const 1).sub hi) (by
      filter_upwards [hpos] with ω hω
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [inv_nonneg.mpr hs.le])))
    (1-Real.exp (-1)) (by
      filter_upwards [] with ω hω
      apply sub_le_sub_left
      apply Real.exp_le_exp.mpr
      have hmul : 1 < s⁻¹ * X ω := by
        rw [← div_eq_inv_mul, lt_div_iff₀ hs]
        simpa using hω
      linarith)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const 1) hi, integral_const, hl _ (inv_pos.mpr hs)] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  have hbnd : P.real {ω | s < X ω} ≤ C / (1-Real.exp (-1)) * s^(-b) := by
    have he := Real.add_one_le_exp (-C * (s⁻¹)^b)
    have hp : (s⁻¹)^b = s^(-b) := by rw [Real.inv_rpow hs.le, Real.rpow_neg hs.le]
    rw [hp] at h he
    apply (le_of_mul_le_mul_right _ hc)
    calc
      _ ≤ 1-Real.exp (-C * s^(-b)) := h
      _ ≤ C * s^(-b) := by linarith
      _ = (C / (1-Real.exp (-1)) * s^(-b)) * (1-Real.exp (-1)) := by field_simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma stable_laplace_inverse_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < (X ω)⁻¹} ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-C*s^b)) := by
  have hi := integrable_exp_neg_mul P hX (hpos.mono fun _ h => h.le) hs.le
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX.inv) hi
    (ae_of_all _ fun _ => (Real.exp_pos _).le) (Real.exp (-1)) (by
      filter_upwards [hpos] with ω hp hω
      apply Real.exp_le_exp.mpr
      have hmul : s * X ω < 1 := by
        simpa only [mul_one] using (lt_inv_mul_iff₀' hp).mp (show s < (X ω)⁻¹ * 1 by simpa using hω)
      linarith)
  rw [hl _ hs] at h
  have hbnd : P.real {ω | s < (X ω)⁻¹} ≤ Real.exp 1 * Real.exp (-C*s^b) := by
    apply le_of_mul_le_mul_right _ (Real.exp_pos (-1))
    calc
      _ ≤ Real.exp (-C*s^b) := h
      _ = (Real.exp 1 * Real.exp (-C*s^b)) * Real.exp (-1) := by
        rw [mul_comm (Real.exp 1), mul_assoc, ← Real.exp_add]
        simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma integrable_rpow_of_power_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K b r : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hrb : r < b)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t < X ω} ≤ ENNReal.ofReal (K*t^(-b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  let B : ℝ → ℝ := fun t => (Ioc (0:ℝ) 1).indicator (fun u => u^(r-1)) t +
    (Ioi (1:ℝ)).indicator (fun u => K*u^(r-b-1)) t
  have h₁ : IntegrableOn (fun t : ℝ => t^(r-1)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have h₂ : IntegrableOn (fun t : ℝ => K*t^(r-b-1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul K
  have hB : Integrable B (volume.restrict (Ioi 0)) :=
    (((integrable_indicator_iff measurableSet_Ioc).mpr h₁).add
      ((integrable_indicator_iff measurableSet_Ioi).mpr h₂)).restrict
  have hBpos : ∀ t, 0 ≤ B t := by
    intro t
    apply add_nonneg
    · exact (indicator_nonneg (s := Ioc (0:ℝ) 1) (fun u hu => Real.rpow_nonneg hu.1.le (r-1))) t
    · exact (indicator_nonneg (s := Ioi (1:ℝ)) (fun u hu => mul_nonneg hK (Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hu)) (r-b-1)))) t
  have hfin := (hasFiniteIntegral_iff_ofReal (ae_of_all _ hBpos)).mp hB.hasFiniteIntegral
  apply lt_of_le_of_lt _ hfin
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  by_cases ht1 : t ≤ 1
  · have hb : B t = t^(r-1) := by
      simp only [B, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht0,ht1⟩),
        indicator_of_notMem (show t ∉ Ioi (1:ℝ) from not_lt.mpr ht1), add_zero]
    rw [hb]
    exact mul_le_of_le_one_left' prob_le_one
  · have hb : B t = K*t^(r-b-1) := by
      simp only [B, indicator_of_notMem (show t ∉ Ioc (0:ℝ) 1 from fun h => ht1 h.2),
        indicator_of_mem (show t ∈ Ioi (1:ℝ) from lt_of_not_ge ht1), zero_add]
    rw [hb]
    calc
      _ ≤ ENNReal.ofReal (K*t^(-b)) * ENNReal.ofReal (t^(r-1)) :=
        mul_le_mul_of_nonneg_right (htail t ht0) zero_le
      _ = ENNReal.ofReal (K*t^(r-b-1)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg ht0.le _)),
          mul_assoc, ← Real.rpow_add ht0]
        rw [show -b + (r-1) = r-b-1 by ring]

lemma integrable_rpow_of_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K C b r : ℝ} (hK : 0 ≤ K) (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (htail : ∀ t : ℝ, 0 < t →
      P {ω | t < X ω} ≤ ENNReal.ofReal (K*Real.exp (-C*t^b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  have hi : IntegrableOn (fun t : ℝ => K * (t^(r-1) * Real.exp (-C*t^b))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) hb hC).const_mul K
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ K * (t^(r-1) * Real.exp (-C*t^b)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hK (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
  apply lt_of_le_of_lt _ ((hasFiniteIntegral_iff_ofReal hnonneg).mp hi.hasFiniteIntegral)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  calc
    _ ≤ ENNReal.ofReal (K*Real.exp (-C*t^b)) * ENNReal.ofReal (t^(r-1)) :=
      mul_le_mul_of_nonneg_right (htail t ht) zero_le
    _ = ENNReal.ofReal (K*(t^(r-1)*Real.exp (-C*t^b))) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_nonneg _))]
      congr 1
      ring

lemma log_sq_le_powers {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    (Real.log x)^2 ≤ (2/r)^2 * (x^r + (x⁻¹)^r) := by
  have he : 0 < r/2 := by positivity
  have hpow (y : ℝ) (hy : 0 ≤ y) : (y^(r/2)/(r/2))^2 = (2/r)^2 * y^r := by
    rw [div_pow, ← Real.rpow_mul_natCast hy]
    norm_num
    field_simp
  by_cases hlog : 0 ≤ Real.log x
  · have h := (sq_le_sq₀ hlog (div_nonneg (Real.rpow_nonneg hx.le _) he.le)).mpr
      (Real.log_le_rpow_div hx.le he)
    rw [hpow x hx.le] at h
    nlinarith [Real.rpow_nonneg (inv_nonneg.mpr hx.le) r, sq_nonneg (2/r)]
  · have hlog' : 0 ≤ Real.log x⁻¹ := by rw [Real.log_inv]; linarith
    have h := (sq_le_sq₀ hlog' (div_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hx.le) _) he.le)).mpr
      (Real.log_le_rpow_div (inv_nonneg.mpr hx.le) he)
    rw [hpow x⁻¹ (inv_nonneg.mpr hx.le), Real.log_inv, neg_sq] at h
    nlinarith [Real.rpow_nonneg hx.le r, sq_nonneg (2/r)]

theorem integrable_log_sq_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω) {r : ℝ} (hr : 0 < r)
    (hi : Integrable (fun ω => X ω ^ r) P)
    (hj : Integrable (fun ω => (X ω)⁻¹ ^ r) P) :
    Integrable (fun ω => (Real.log (X ω))^2) P := by
  apply ((hi.add hj).const_mul ((2/r)^2)).mono' ((hX.log.pow_const 2).aestronglyMeasurable)
  filter_upwards [hpos] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact log_sq_le_powers hω hr

lemma stable_positive_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b r : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hrb : r < b)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => X ω ^ r) P := by
  apply integrable_rpow_of_power_tail P hX hpos (K := C/(1-Real.exp (-1)))
    (div_nonneg hC.le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))) hr hrb
  exact fun _ ht => stable_laplace_upper_tail P hX hpos hl ht

lemma stable_negative_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b r : ℝ}
    (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => (X ω)⁻¹ ^ r) P := by
  apply integrable_rpow_of_exp_tail P hX.inv (hpos.mono fun _ h => (inv_pos.mpr h).le)
    (Real.exp_nonneg 1) hC hb hr
  exact fun _ ht => stable_laplace_inverse_tail P hX hpos hl ht

lemma negExp_eq_exp_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : negExp x = Real.exp (-x.toReal) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hx, negExp_ofReal ENNReal.toReal_nonneg]

lemma poissonTotal_real_laplace {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {t : ℝ} (ht : 0 < t) :
    (∫ ν, Real.exp (-t * (poissonTotal ν).toReal) ∂poissonLaw (powerIntensity b)) =
    Real.exp (-(stableLaplaceConstant b).toReal * t^b) := by
  calc
    _ = ∫ ν, negExp (ENNReal.ofReal t * poissonTotal ν) ∂poissonLaw (powerIntensity b) := by
      apply integral_congr_ae
      filter_upwards [poissonTotal_finite_positive hb hb1] with ν hν
      rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν.2.ne),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le, neg_mul]
    _ = _ := by
      rw [poissonTotal_laplace b ht,
        negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (stableLaplaceConstant_lt_top hb hb1).ne),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le b)]
      congr 1
      ring

lemma poissonTotal_real_pos {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∀ᵐ ν ∂poissonLaw (powerIntensity b), 0 < (poissonTotal ν).toReal := by
  filter_upwards [poissonTotal_finite_positive hb hb1] with ν hν
  exact ENNReal.toReal_pos hν.1.ne' hν.2.ne

lemma poissonTotal_positive_moment {b r : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hr : 0 < r) (hrb : r < b) :
    Integrable (fun ν => (poissonTotal ν).toReal ^ r) (poissonLaw (powerIntensity b)) :=
  stable_positive_moment _ measurable_poissonTotal.ennreal_toReal
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
    (ENNReal.toReal_pos (stableLaplaceConstant_pos hb).ne' (stableLaplaceConstant_lt_top hb hb1).ne)
    hr hrb (fun _ ht => poissonTotal_real_laplace hb hb1 ht)

lemma poissonTotal_negative_moment {b r : ℝ} (hb : 0 < b) (hb1 : b < 1) (hr : 0 < r) :
    Integrable (fun ν => ((poissonTotal ν).toReal)⁻¹ ^ r) (poissonLaw (powerIntensity b)) :=
  stable_negative_moment _ measurable_poissonTotal.ennreal_toReal
    (poissonTotal_real_pos hb hb1)
    (ENNReal.toReal_pos (stableLaplaceConstant_pos hb).ne' (stableLaplaceConstant_lt_top hb hb1).ne)
    hb hr (fun _ ht => poissonTotal_real_laplace hb hb1 ht)

theorem poissonTotal_log_square {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable (fun ν => (Real.log (poissonTotal ν).toReal)^2) (poissonLaw (powerIntensity b)) :=
  integrable_log_sq_of_moments _ measurable_poissonTotal.ennreal_toReal
    (poissonTotal_real_pos hb hb1) (show 0 < b/2 by linarith)
    (poissonTotal_positive_moment hb hb1 (by linarith) (by linarith))
    (poissonTotal_negative_moment hb hb1 (by linarith))

end IsingPerceptron

end

end OAI

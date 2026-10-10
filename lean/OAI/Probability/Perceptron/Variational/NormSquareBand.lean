import Mathlib
import OAI.Probability.Perceptron.Sphere.SphereIsometryMap
import OAI.Probability.Perceptron.Pressure.FiniteTerminal

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma canonicalRadial_upper_tail (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    canonicalRadialMass n 1 {x | ((n+1 : ℕ) : ℝ)*(1+ε) ≤ ‖x‖^2} ≤
      ENNReal.ofReal (Real.exp (-((ε-Real.log (1+ε))/2)*((n+1 : ℕ) : ℝ))) := by
  have hd : 0 < 1+ε := by linarith
  have hb : 0 ≤ 1-(1+ε)⁻¹ := by
    apply sub_nonneg.mpr
    exact (inv_le_one₀ hd).mpr (by linarith)
  have hid : (1-(1+ε)⁻¹)*(1+ε) = ε := by field_simp; ring
  have h := canonicalRadial_mass_le (n := n) (a := 1) (b := (1+ε)⁻¹)
    (A := {x | ((n+1 : ℕ) : ℝ)*(1+ε) ≤ ‖x‖^2})
    (c := -((n+1 : ℕ) : ℝ)*ε/2) (by norm_num) (inv_pos.mpr hd)
    (measurableSet_le measurable_const (continuous_norm.pow 2).measurable) (by
      intro x hx
      have hh := mul_le_mul_of_nonneg_left hx hb
      have he : (1-(1+ε)⁻¹)*(((n+1 : ℕ) : ℝ)*(1+ε)) = ((n+1 : ℕ) : ℝ)*ε := by
        calc
          _ = ((n+1 : ℕ) : ℝ)*((1-(1+ε)⁻¹)*(1+ε)) := by ring
          _ = _ := by rw [hid]
      rw [he] at hh
      nlinarith)
  convert h using 1
  congr 1
  rw [Real.rpow_def_of_pos (inv_pos.mpr hd),Real.log_inv,← Real.exp_add]
  congr 1
  ring

lemma canonicalRadial_lower_tail (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    canonicalRadialMass n 1 {x | ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1-ε)} ≤
      ENNReal.ofReal (Real.exp (-((-ε-Real.log (1-ε))/2)*((n+1 : ℕ) : ℝ))) := by
  have hd : 0 < 1-ε := sub_pos.mpr hε1
  have hb : 0 ≤ (1-ε)⁻¹-1 := by
    apply sub_nonneg.mpr
    exact (one_le_inv₀ hd).mpr (by linarith)
  have hid : ((1-ε)⁻¹-1)*(1-ε) = ε := by field_simp; ring
  have h := canonicalRadial_mass_le (n := n) (a := 1) (b := (1-ε)⁻¹)
    (A := {x | ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1-ε)})
    (c := ((n+1 : ℕ) : ℝ)*ε/2) (by norm_num) (inv_pos.mpr hd)
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const) (by
      intro x hx
      have hh := mul_le_mul_of_nonneg_left hx hb
      have he : ((1-ε)⁻¹-1)*(((n+1 : ℕ) : ℝ)*(1-ε)) = ((n+1 : ℕ) : ℝ)*ε := by
        calc
          _ = ((n+1 : ℕ) : ℝ)*(((1-ε)⁻¹-1)*(1-ε)) := by ring
          _ = _ := by rw [hid]
      rw [he] at hh
      nlinarith)
  convert h using 1
  congr 1
  rw [Real.rpow_def_of_pos (inv_pos.mpr hd),Real.log_inv,← Real.exp_add]
  congr 1
  ring

def normSquareBand (n : ℕ) (ε : ℝ) : Set (RadialSpace n) :=
  {x | ((n+1 : ℕ) : ℝ)*(1-ε) ≤ ‖x‖^2 ∧ ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1+ε)}

lemma normSquareBand_measurable (n : ℕ) (ε : ℝ) : MeasurableSet (normSquareBand n ε) :=
  (measurableSet_le measurable_const (continuous_norm.pow 2).measurable).inter
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const)

lemma canonicalRadial_band_compl_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    canonicalRadialMass n 1 (normSquareBand n ε)ᶜ ≤
      ENNReal.ofReal (Real.exp (-((ε-Real.log (1+ε))/2)*((n+1 : ℕ) : ℝ)))+
      ENNReal.ofReal (Real.exp (-((-ε-Real.log (1-ε))/2)*((n+1 : ℕ) : ℝ))) := by
  calc
    _ ≤ canonicalRadialMass n 1
        ({x | ((n+1 : ℕ) : ℝ)*(1+ε) ≤ ‖x‖^2} ∪ {x | ‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*(1-ε)}) :=
      measure_mono (by
        intro x hx
        change ¬ (_ ∧ _) at hx
        rcases not_and_or.mp hx with h | h
        · exact Or.inr (le_of_not_ge h)
        · exact Or.inl (le_of_not_ge h))
    _ ≤ _ := (measure_union_le _ _).trans
      (add_le_add (canonicalRadial_upper_tail n hε) (canonicalRadial_lower_tail n hε hε1))

lemma exp_neg_mul_nat_succ_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

lemma canonicalRadial_band_eventually_half {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, (1/2 : ℝ) ≤ (canonicalRadialMass n 1).real (normSquareBand n ε) := by
  have hu : 0 < (ε-Real.log (1+ε))/2 := by
    have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1+ε) (by linarith : 1+ε ≠ 1)
    linarith
  have hl : 0 < (-ε-Real.log (1-ε))/2 := by
    have h := Real.log_lt_sub_one_of_pos (by linarith : 0 < 1-ε) (by linarith : 1-ε ≠ 1)
    linarith
  have ht := (exp_neg_mul_nat_succ_tendsto hu).add (exp_neg_mul_nat_succ_tendsto hl)
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.exp (-((ε-Real.log (1+ε))/2)*((n+1 : ℕ) : ℝ))+
      Real.exp (-((-ε-Real.log (1-ε))/2)*((n+1 : ℕ) : ℝ)) < 1/2 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)+0 < 1/2))
  filter_upwards [hev] with n hn
  have h := canonicalRadial_band_compl_le n hε hε1
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le] at h
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at h'
  change (canonicalRadialMass n 1).real (normSquareBand n ε)ᶜ ≤ _ at h'
  rw [measureReal_compl (normSquareBand_measurable n ε), probReal_univ] at h'
  linarith

lemma canonicalRadialMass_real_apply {n : ℕ} {b : ℝ} (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) :
    (canonicalRadialMass n b).real A = ∫ x in A, canonicalRadialDensity n b x := by
  rw [Measure.real,canonicalRadialMass_apply hb hA,ENNReal.toReal_ofReal]
  exact integral_nonneg fun x => (canonicalRadialDensity_pos n b x).le

lemma canonicalRadialDensity_tilt (n : ℕ) (b : ℝ) (x : RadialSpace n) :
    canonicalRadialDensity n b x = Real.exp (((1-b)/2)*‖x‖^2)*canonicalRadialDensity n 1 x := by
  unfold canonicalRadialDensity
  rw [mul_left_comm (Real.exp _) (radialNormalizer n),← Real.exp_add]
  congr 2
  ring

lemma normSquareBand_tilt_bounds (n : ℕ) {ε b : ℝ} {x : RadialSpace n}
    (hx : x ∈ normSquareBand n ε) :
    ((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2) ≤ ((1-b)/2)*‖x‖^2 ∧
    ((1-b)/2)*‖x‖^2 ≤ ((n+1 : ℕ) : ℝ)*((1-b)/2+|1-b| *ε/2) := by
  have ha : |‖x‖^2-((n+1 : ℕ) : ℝ)| ≤ ((n+1 : ℕ) : ℝ)*ε := by
    rcases hx with ⟨hl,hu⟩
    apply abs_le.mpr
    constructor <;> nlinarith
  have hm := mul_le_mul_of_nonneg_left ha (abs_nonneg (1-b))
  rw [← abs_mul] at hm
  obtain ⟨hl,hu⟩ := abs_le.mp hm
  constructor <;> nlinarith

lemma canonicalRadial_band_mass_bounds (n : ℕ) {b ε : ℝ} (hb : 0 < b)
    (hhalf : (1/2 : ℝ) ≤ (canonicalRadialMass n 1).real (normSquareBand n ε)) :
    Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))/2 ≤
      (canonicalRadialMass n b).real (normSquareBand n ε) ∧
    (canonicalRadialMass n b).real (normSquareBand n ε) ≤
      Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2+|1-b| *ε/2)) := by
  have hm := normSquareBand_measurable n ε
  have hlo : Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))*
      (canonicalRadialMass n 1).real (normSquareBand n ε) ≤
      (canonicalRadialMass n b).real (normSquareBand n ε) := by
    rw [canonicalRadialMass_real_apply hb hm,canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) hm,
      ← integral_const_mul]
    apply setIntegral_mono_on
      ((canonicalRadialDensity_integrable n (by norm_num : (0:ℝ)<1)).const_mul _).integrableOn
      (canonicalRadialDensity_integrable n hb).integrableOn hm
    intro x hx
    rw [canonicalRadialDensity_tilt n b x]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (normSquareBand_tilt_bounds n hx).1)
      (canonicalRadialDensity_pos n 1 x).le
  have hup : (canonicalRadialMass n b).real (normSquareBand n ε) ≤
      Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2+|1-b| *ε/2))*
      (canonicalRadialMass n 1).real (normSquareBand n ε) := by
    rw [canonicalRadialMass_real_apply hb hm,canonicalRadialMass_real_apply (by norm_num : (0:ℝ)<1) hm,
      ← integral_const_mul]
    apply setIntegral_mono_on
      (canonicalRadialDensity_integrable n hb).integrableOn
      ((canonicalRadialDensity_integrable n (by norm_num : (0:ℝ)<1)).const_mul _).integrableOn hm
    intro x hx
    rw [canonicalRadialDensity_tilt n b x]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (normSquareBand_tilt_bounds n hx).2)
      (canonicalRadialDensity_pos n 1 x).le
  constructor
  · have h := mul_le_mul_of_nonneg_left hhalf (Real.exp_pos (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))).le
    have h' : Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))/2 ≤
        Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))*
        (canonicalRadialMass n 1).real (normSquareBand n ε) := by simpa only [mul_one_div] using h
    exact h'.trans hlo
  · apply hup.trans
    exact mul_le_of_le_one_right (Real.exp_pos _).le (measureReal_le_one)

lemma canonicalRadial_band_log_bounds (n : ℕ) {b ε : ℝ} (hb : 0 < b)
    (hhalf : (1/2 : ℝ) ≤ (canonicalRadialMass n 1).real (normSquareBand n ε)) :
    (1-b)/2-|1-b| *ε/2-Real.log 2/((n+1 : ℕ) : ℝ) ≤
      Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ∧
    Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ≤
      (1-b)/2+|1-b| *ε/2 := by
  obtain ⟨hl,hu⟩ := canonicalRadial_band_mass_bounds n hb hhalf
  have hlpos : 0 < Real.exp (((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2))/2 := by positivity
  have hmpos := hlpos.trans_le hl
  have hl' := Real.log_le_log hlpos hl
  have hu' := Real.log_le_log hmpos hu
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2:ℝ) ≠ 0),Real.log_exp] at hl'
  rw [Real.log_exp] at hu'
  have hn : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  constructor
  · apply (le_div_iff₀ hn).mpr
    have he : ((1-b)/2-|1-b| *ε/2-Real.log 2/((n+1 : ℕ) : ℝ))*((n+1 : ℕ) : ℝ) =
        ((n+1 : ℕ) : ℝ)*((1-b)/2-|1-b| *ε/2)-Real.log 2 := by field_simp
    rw [he]
    exact hl'
  · exact (div_le_iff₀ hn).mpr (by nlinarith)

lemma canonicalRadial_band_log_eventually {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop,
      (1-b)/2-|1-b| *ε/2-Real.log 2/((n+1 : ℕ) : ℝ) ≤
        Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ∧
      Real.log ((canonicalRadialMass n b).real (normSquareBand n ε))/((n+1 : ℕ) : ℝ) ≤
        (1-b)/2+|1-b| *ε/2 :=
  (canonicalRadial_band_eventually_half hε hε1).mono fun n hn => canonicalRadial_band_log_bounds n hb hn

lemma unitSphere_continuous_integrable {n : ℕ}
    {f : Metric.sphere (0 : Spin (n+1)) 1 → ℝ} (hf : Continuous f) :
    Integrable f (unitSphereLaw (n+1)) := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun u => hC u (mem_univ _))

def sphericalExp (n : ℕ) (z : Spin (n+1)) (r : ℝ) : ℝ :=
  ∫ u : Metric.sphere (0 : Spin (n+1)) 1, Real.exp (r * inner ℝ z (u:Spin (n+1))) ∂unitSphereLaw (n+1)

lemma sphericalExp_even (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    sphericalExp n z (-r) = sphericalExp n z r := by
  have hemb : MeasurableEmbedding (sphereIsometryMap (LinearIsometryEquiv.neg ℝ : Spin (n+1) ≃ₗᵢ[ℝ] Spin (n+1))) := by
    apply Measurable.measurableEmbedding
      (sphereIsometryMap_measurable _) _
    intro u v huv
    apply Subtype.ext
    have := congrArg Subtype.val huv
    simpa [sphereIsometryMap] using this
  have h := (unitSphereLaw_isometry_preserving (LinearIsometryEquiv.neg ℝ : Spin (n+1) ≃ₗᵢ[ℝ] Spin (n+1))).integral_comp hemb
    (fun u : Metric.sphere (0:Spin (n+1)) 1 => Real.exp (r * inner ℝ z (u:Spin (n+1))))
  simpa [sphericalExp,sphereIsometryMap] using h

lemma sphericalExp_eq_cosh (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    sphericalExp n z r =
      ∫ u : Metric.sphere (0 : Spin (n+1)) 1, Real.cosh (r * inner ℝ z (u:Spin (n+1))) ∂unitSphereLaw (n+1) := by
  have hi (s : ℝ) : Integrable (fun u : Metric.sphere (0:Spin (n+1)) 1 => Real.exp (s * inner ℝ z (u:Spin (n+1)))) (unitSphereLaw (n+1)) :=
    unitSphere_continuous_integrable (by fun_prop)
  simp only [Real.cosh_eq,integral_div]
  rw [integral_add (hi r) (by simpa only [neg_mul] using hi (-r))]
  simp only [← neg_mul]
  change sphericalExp n z r = (sphericalExp n z r + sphericalExp n z (-r))/2
  rw [sphericalExp_even]
  ring

lemma sphericalExp_mono (n : ℕ) (z : Spin (n+1)) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) : sphericalExp n z r ≤ sphericalExp n z s := by
  rw [sphericalExp_eq_cosh,sphericalExp_eq_cosh]
  apply integral_mono (unitSphere_continuous_integrable (by fun_prop))
    (unitSphere_continuous_integrable (by fun_prop))
  intro u
  apply Real.cosh_le_cosh.mpr
  rw [abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg (hr.trans hrs)]
  exact mul_le_mul_of_nonneg_right hrs (abs_nonneg _)

lemma one_le_sphericalExp (n : ℕ) (z : Spin (n+1)) (r : ℝ) :
    1 ≤ sphericalExp n z r := by
  rw [sphericalExp_eq_cosh]
  calc
    (1:ℝ) = ∫ _ : Metric.sphere (0:Spin (n+1)) 1, (1:ℝ) ∂unitSphereLaw (n+1) := by simp
    _ ≤ _ := integral_mono (integrable_const _) (unitSphere_continuous_integrable (by fun_prop)) (fun u => Real.one_le_cosh _)

section Polar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma polar_lintegral (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ u : Metric.sphere (0:E) 1, ∫⁻ r : Ioi (0:ℝ),
        f ((r:ℝ) • (u:E)) ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂μ.toSphere := by
  let h := homeomorphUnitSphereProd E
  let F : Metric.sphere (0:E) 1 × Ioi (0:ℝ) → ℝ≥0∞ :=
    fun p => f ((p.2:ℝ) • (p.1:E))
  have hF : Measurable F := hf.comp (measurable_snd.subtype_val.smul measurable_fst.subtype_val)
  calc
    _ = ∫⁻ x : ({(0:E)}ᶜ : Set E), f (x:E) ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫⁻ p, F p ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      convert (μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp hF) using 1
      apply lintegral_congr
      intro x
      change f (x:E) = f ((h x).2.val • (h x).1.val)
      have he := congrArg Subtype.val (h.symm_apply_apply x)
      exact congrArg f he.symm
    _ = _ := lintegral_prod _ hF.aemeasurable

lemma polar_lintegral_swap (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ r : Ioi (0:ℝ), ∫⁻ u : Metric.sphere (0:E) 1,
        f ((r:ℝ) • (u:E)) ∂μ.toSphere ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) := by
  rw [polar_lintegral μ f hf]
  exact lintegral_lintegral_swap
    (hf.comp (measurable_snd.subtype_val.smul measurable_fst.subtype_val)).aemeasurable

def normalizedAngular : Measure (Metric.sphere (0:E) 1) :=
  (μ.toSphere univ)⁻¹ • μ.toSphere

def haarRadiusMeasure : Measure (Ioi (0:ℝ)) :=
  μ.toSphere univ • Measure.volumeIoiPow (Module.finrank ℝ E - 1)

lemma angular_total_ne_zero : μ.toSphere univ ≠ 0 := by
  exact Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero μ)

lemma polar_lintegral_normalized (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ r : Ioi (0:ℝ), ∫⁻ u : Metric.sphere (0:E) 1,
        f ((r:ℝ) • (u:E)) ∂normalizedAngular μ ∂haarRadiusMeasure μ := by
  rw [haarRadiusMeasure,lintegral_smul_measure]
  simp only [normalizedAngular,lintegral_smul_measure,smul_eq_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (angular_total_ne_zero μ)),← mul_assoc,
    ENNReal.mul_inv_cancel (angular_total_ne_zero μ) (measure_ne_top _ _),one_mul]
  exact polar_lintegral_swap μ f hf

lemma polar_radial_lintegral (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g ‖x‖ ∂μ) = ∫⁻ r : Ioi (0:ℝ), g r ∂haarRadiusMeasure μ := by
  rw [polar_lintegral_normalized μ (fun x => g ‖x‖) (hg.comp measurable_norm)]
  apply lintegral_congr
  intro r
  have hnorm (u : Metric.sphere (0:E) 1) : ‖(r:ℝ) • (u:E)‖ = (r:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property]
    simp
  simp only [hnorm,lintegral_const,normalizedAngular,Measure.smul_apply,smul_eq_mul]
  rw [ENNReal.inv_mul_cancel (angular_total_ne_zero μ) (measure_ne_top _ _),mul_one]

lemma polar_weighted_lintegral (f : E → ℝ≥0∞) (hf : Measurable f)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g ‖x‖ * f x ∂μ) =
      ∫⁻ r : Ioi (0:ℝ), g r * (∫⁻ u : Metric.sphere (0:E) 1,
        f ((r:ℝ) • (u:E)) ∂normalizedAngular μ) ∂haarRadiusMeasure μ := by
  rw [polar_lintegral_normalized μ (fun x => g ‖x‖ * f x) ((hg.comp measurable_norm).mul hf)]
  apply lintegral_congr
  intro r
  have hnorm (u : Metric.sphere (0:E) 1) : ‖(r:ℝ) • (u:E)‖ = (r:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property]; simp
  simp only [hnorm]
  exact lintegral_const_mul _ ((hf.comp (measurable_subtype_coe.const_smul (r:ℝ))))

lemma polar_weighted_bounds (f : E → ℝ≥0∞) (hf : Measurable f)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) {L U : ℝ≥0∞}
    (hL : ∀ r : Ioi (0:ℝ), g r ≠ 0 →
      L ≤ ∫⁻ u : Metric.sphere (0:E) 1, f ((r:ℝ) • (u:E)) ∂normalizedAngular μ)
    (hU : ∀ r : Ioi (0:ℝ), g r ≠ 0 →
      (∫⁻ u : Metric.sphere (0:E) 1, f ((r:ℝ) • (u:E)) ∂normalizedAngular μ) ≤ U) :
    L * (∫⁻ x, g ‖x‖ ∂μ) ≤ (∫⁻ x, g ‖x‖ * f x ∂μ) ∧
      (∫⁻ x, g ‖x‖ * f x ∂μ) ≤ U * (∫⁻ x, g ‖x‖ ∂μ) := by
  rw [polar_radial_lintegral μ g hg,polar_weighted_lintegral μ f hf g hg]
  constructor
  · rw [← lintegral_const_mul (f := fun r : Ioi (0:ℝ) => g r) _ (hg.comp measurable_subtype_coe)]
    apply lintegral_mono
    intro r
    by_cases hr : g r = 0
    · simp [hr]
    · simpa only [mul_comm L] using mul_le_mul le_rfl (hL r hr) (by positivity) (by positivity)
  · rw [← lintegral_const_mul (f := fun r : Ioi (0:ℝ) => g r) _ (hg.comp measurable_subtype_coe)]
    apply lintegral_mono
    intro r
    by_cases hr : g r = 0
    · simp [hr]
    · simpa only [mul_comm U] using mul_le_mul le_rfl (hU r hr) (by positivity) (by positivity)

end Polar

def linearFieldFactor {n : ℕ} (ρ : Measure (Spin (n+1))) (x : Spin (n+1)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ z x)) ∂ρ

def angularFieldFactor {n : ℕ} (ρ : Measure (Spin (n+1))) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u : Metric.sphere (0:Spin (n+1)) 1,
    linearFieldFactor ρ (r • (u:Spin (n+1))) ∂unitSphereLaw (n+1)

lemma linearFieldFactor_measurable {n : ℕ} (ρ : Measure (Spin (n+1))) [SFinite ρ] :
    Measurable (linearFieldFactor ρ) := by
  exact Measurable.lintegral_prod_right
    ((continuous_snd.inner continuous_fst).rexp.measurable.ennreal_ofReal)

lemma angularFieldFactor_eq {n : ℕ} (ρ : Measure (Spin (n+1))) [SFinite ρ] (r : ℝ) :
    angularFieldFactor ρ r = ∫⁻ z, ENNReal.ofReal (sphericalExp n z r) ∂ρ := by
  unfold angularFieldFactor linearFieldFactor
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro z
  simp only [inner_smul_right]
  exact (ofReal_integral_eq_lintegral_ofReal
    (unitSphere_continuous_integrable (by fun_prop))
    (Eventually.of_forall fun u => (Real.exp_pos _).le)).symm

lemma angularFieldFactor_mono {n : ℕ} (ρ : Measure (Spin (n+1))) [SFinite ρ]
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    angularFieldFactor ρ r ≤ angularFieldFactor ρ s := by
  rw [angularFieldFactor_eq,angularFieldFactor_eq]
  exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal (sphericalExp_mono n z hr hrs)

lemma one_le_angularFieldFactor {n : ℕ} (ρ : Measure (Spin (n+1))) [IsProbabilityMeasure ρ]
    (r : ℝ) : 1 ≤ angularFieldFactor ρ r := by
  rw [angularFieldFactor_eq]
  calc
    (1:ℝ≥0∞) = ∫⁻ _ : Spin (n+1), (1:ℝ≥0∞) ∂ρ := by simp
    _ ≤ _ := lintegral_mono fun z => by
      simpa using ENNReal.ofReal_le_ofReal (one_le_sphericalExp n z r)

def canonicalBandRadiusWeight (n : ℕ) (b ε : ℝ) : ℝ → ℝ≥0∞ :=
  {r : ℝ | ((n+1:ℕ):ℝ)*(1-ε) ≤ r^2 ∧ r^2 ≤ ((n+1:ℕ):ℝ)*(1+ε)}.indicator
    (fun r => ENNReal.ofReal (radialNormalizer n * Real.exp (-(b/2)*r^2)))

lemma canonicalBandRadiusWeight_measurable (n : ℕ) (b ε : ℝ) :
    Measurable (canonicalBandRadiusWeight n b ε) := by
  apply Measurable.indicator (by fun_prop)
  exact (measurableSet_le measurable_const (continuous_id.pow 2).measurable).inter
    (measurableSet_le (continuous_id.pow 2).measurable measurable_const)

lemma canonicalBandRadiusWeight_integral (n : ℕ) (b ε : ℝ)
    (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, canonicalBandRadiusWeight n b ε ‖x‖ * F x) =
      ∫⁻ x in normSquareBand n ε, F x ∂canonicalRadialMass n b := by
  rw [canonicalRadialMass,setLIntegral_withDensity_eq_setLIntegral_mul _
    (canonicalRadialDensity_continuous n b).measurable.ennreal_ofReal hF
    (normSquareBand_measurable n ε),← lintegral_indicator (normSquareBand_measurable n ε) _]
  apply lintegral_congr
  intro x
  by_cases hx : ((n+1:ℕ):ℝ)*(1-ε) ≤ ‖x‖^2 ∧ ‖x‖^2 ≤ ((n+1:ℕ):ℝ)*(1+ε)
  all_goals simp only [canonicalBandRadiusWeight,normSquareBand,Set.indicator_apply,Set.mem_ofPred_eq,hx,and_self,ite_true,ite_false,zero_mul,Pi.mul_apply,canonicalRadialDensity]

end SphericalPerceptronFreeEnergy

end

end OAI

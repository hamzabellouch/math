import Mathlib

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

abbrev RadialSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n+1))

def radialNormalizer (n : ℕ) : ℝ := ((2*Real.pi)^(((n+1 : ℕ) : ℝ)/2))⁻¹

def canonicalRadialDensity (n : ℕ) (b : ℝ) (x : RadialSpace n) : ℝ :=
  radialNormalizer n * Real.exp (-(b/2)*‖x‖^2)

def canonicalRadialMass (n : ℕ) (b : ℝ) : Measure (RadialSpace n) :=
  volume.withDensity (fun x => ENNReal.ofReal (canonicalRadialDensity n b x))

lemma radialNormalizer_pos (n : ℕ) : 0 < radialNormalizer n := by
  unfold radialNormalizer
  positivity

lemma canonicalRadialDensity_pos (n : ℕ) (b : ℝ) (x : RadialSpace n) :
    0 < canonicalRadialDensity n b x := mul_pos (radialNormalizer_pos n) (Real.exp_pos _)

lemma canonicalRadialDensity_continuous (n : ℕ) (b : ℝ) :
    Continuous (canonicalRadialDensity n b) := by unfold canonicalRadialDensity; fun_prop

lemma integrable_exp_neg_norm_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : RadialSpace n => Real.exp (-(b/2)*‖x‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := ((b/2 : ℝ) : ℂ)) (by simpa using half_pos hb) 0 (0 : RadialSpace n)).re
  convert h using 1
  ext x
  simp only [zero_mul,add_zero,← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_neg,
    ]
  exact (Complex.exp_ofReal_re _).symm

lemma canonicalRadialDensity_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (canonicalRadialDensity n b) :=
  (integrable_exp_neg_norm_sq n hb).const_mul _

lemma canonicalRadialDensity_integral (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x, canonicalRadialDensity n b x) = b ^ (-((n+1 : ℕ) : ℝ)/2) := by
  simp only [canonicalRadialDensity]
  rw [integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (half_pos hb)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [show Real.pi/(b/2) = (2*Real.pi)/b by ring,Real.div_rpow (by positivity) hb.le]
  unfold radialNormalizer
  rw [show -((n+1 : ℕ) : ℝ)/2 = -(((n+1 : ℕ) : ℝ)/2) by ring, Real.rpow_neg hb.le]
  field_simp

instance (n : ℕ) : IsProbabilityMeasure (canonicalRadialMass n 1) := by
  constructor
  rw [canonicalRadialMass,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,← ofReal_integral_eq_lintegral_ofReal
      (canonicalRadialDensity_integrable n (by norm_num : (0:ℝ)<1))
      (Eventually.of_forall fun x => (canonicalRadialDensity_pos n 1 x).le),
    canonicalRadialDensity_integral n (by norm_num : (0:ℝ)<1)]
  simp

lemma canonicalRadialMass_apply {n : ℕ} {b : ℝ} (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) :
    canonicalRadialMass n b A = ENNReal.ofReal (∫ x in A, canonicalRadialDensity n b x) := by
  rw [canonicalRadialMass,withDensity_apply _ hA]
  exact (ofReal_integral_eq_lintegral_ofReal (canonicalRadialDensity_integrable n hb).integrableOn
    (Eventually.of_forall fun x => (canonicalRadialDensity_pos n b x).le)).symm

lemma canonicalRadial_mass_le {n : ℕ} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A)
    (hc : ∀ x ∈ A, -(a/2)*‖x‖^2 ≤ c-(b/2)*‖x‖^2) :
    canonicalRadialMass n a A ≤ ENNReal.ofReal (Real.exp c * b ^ (-((n+1 : ℕ) : ℝ)/2)) := by
  rw [canonicalRadialMass_apply ha hA]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ x in A, Real.exp c * canonicalRadialDensity n b x := by
      apply setIntegral_mono_on (canonicalRadialDensity_integrable n ha).integrableOn
        ((canonicalRadialDensity_integrable n hb).const_mul _).integrableOn hA
      intro x hx
      unfold canonicalRadialDensity
      calc
        _ ≤ radialNormalizer n * Real.exp (c-(b/2)*‖x‖^2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hc x hx)) (radialNormalizer_pos n).le
        _ = _ := by rw [Real.exp_sub,neg_mul,Real.exp_neg]; ring
    _ ≤ ∫ x, Real.exp c * canonicalRadialDensity n b x := by
      apply setIntegral_le_integral ((canonicalRadialDensity_integrable n hb).const_mul _)
      exact Eventually.of_forall fun x => (mul_pos (Real.exp_pos c) (canonicalRadialDensity_pos n b x)).le
    _ = _ := by rw [integral_const_mul,canonicalRadialDensity_integral n hb]

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

end SphericalPerceptron
end
end
end

end OAI

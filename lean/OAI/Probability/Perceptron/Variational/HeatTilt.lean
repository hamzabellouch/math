import Mathlib
import OAI.Probability.Perceptron.Variational.StableLaplaceConstant
import OAI.Probability.Perceptron.Variational.NormSquareBand

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

lemma canonicalBandRadiusWeight_mass (n : ℕ) (b ε : ℝ) :
    (∫⁻ x : RadialSpace n, canonicalBandRadiusWeight n b ε ‖x‖) =
      canonicalRadialMass n b (normSquareBand n ε) := by
  simpa using canonicalBandRadiusWeight_integral n b ε (fun _ => 1) measurable_const

lemma canonicalField_band_bounds (n : ℕ) (b ε : ℝ)
    (ρ : Measure (Spin (n+1))) [SFinite ρ] :
    angularFieldFactor ρ (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))) *
      canonicalRadialMass n b (normSquareBand n ε) ≤
        (∫⁻ x in normSquareBand n ε, linearFieldFactor ρ x ∂canonicalRadialMass n b) ∧
    (∫⁻ x in normSquareBand n ε, linearFieldFactor ρ x ∂canonicalRadialMass n b) ≤
      angularFieldFactor ρ (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))) *
        canonicalRadialMass n b (normSquareBand n ε) := by
  have hh := polar_weighted_bounds (volume : Measure (RadialSpace n))
    (linearFieldFactor ρ) (linearFieldFactor_measurable ρ)
    (canonicalBandRadiusWeight n b ε) (canonicalBandRadiusWeight_measurable n b ε)
    (L := angularFieldFactor ρ (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))))
    (U := angularFieldFactor ρ (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))))
  rw [canonicalBandRadiusWeight_integral n b ε _ (linearFieldFactor_measurable ρ),
    canonicalBandRadiusWeight_mass] at hh
  apply hh
  · intro r hr
    have hb : ((n+1:ℕ):ℝ)*(1-ε) ≤ (r:ℝ)^2 ∧ (r:ℝ)^2 ≤ ((n+1:ℕ):ℝ)*(1+ε) := by
      by_contra hn
      exact hr (by simp only [canonicalBandRadiusWeight,Set.indicator_apply,Set.mem_ofPred_eq,hn,ite_false])
    change angularFieldFactor ρ _ ≤ angularFieldFactor ρ (r:ℝ)
    apply angularFieldFactor_mono ρ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_iff).mpr ⟨r.property.le,hb.1⟩
  · intro r hr
    have hb : ((n+1:ℕ):ℝ)*(1-ε) ≤ (r:ℝ)^2 ∧ (r:ℝ)^2 ≤ ((n+1:ℕ):ℝ)*(1+ε) := by
      by_contra hn
      exact hr (by simp only [canonicalBandRadiusWeight,Set.indicator_apply,Set.mem_ofPred_eq,hn,ite_false])
    change angularFieldFactor ρ (r:ℝ) ≤ angularFieldFactor ρ _
    apply angularFieldFactor_mono ρ r.property.le
    exact (Real.le_sqrt' r.property).mpr hb.2

lemma canonicalWeighted_mass_le (n : ℕ) (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F)
    {A : Set (RadialSpace n)} (hA : MeasurableSet A) {a b c : ℝ}
    (hc : ∀ x ∈ A, -(a/2)*‖x‖^2 ≤ c-(b/2)*‖x‖^2) :
    (∫⁻ x in A, F x ∂canonicalRadialMass n a) ≤
      ENNReal.ofReal (Real.exp c) * (∫⁻ x, F x ∂canonicalRadialMass n b) := by
  have hd (d : ℝ) : Measurable (fun x : RadialSpace n => ENNReal.ofReal (canonicalRadialDensity n d x)) :=
    (canonicalRadialDensity_continuous n d).measurable.ennreal_ofReal
  rw [canonicalRadialMass,setLIntegral_withDensity_eq_setLIntegral_mul _ (hd a) hF hA,
    canonicalRadialMass,lintegral_withDensity_eq_lintegral_mul _ (hd b) hF,
    ← lintegral_const_mul _ ((hd b).mul hF)]
  calc
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (Real.exp c) *
        (ENNReal.ofReal (canonicalRadialDensity n b x) * F x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      change ENNReal.ofReal (canonicalRadialDensity n a x) * F x ≤ _
      rw [← mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos c).le]
      apply mul_le_mul (ENNReal.ofReal_le_ofReal ?_) le_rfl (by positivity) (by positivity)
      unfold canonicalRadialDensity
      calc
        _ ≤ radialNormalizer n * Real.exp (c-(b/2)*‖x‖^2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hc x hx)) (radialNormalizer_pos n).le
        _ = _ := by rw [Real.exp_sub,neg_mul,Real.exp_neg]; ring
    _ ≤ _ := setLIntegral_le_lintegral _ _

lemma canonicalWeighted_upper_tail (n : ℕ) (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F)
    (b ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ x in {x : RadialSpace n | ((n+1:ℕ):ℝ)*(1+ε) ≤ ‖x‖^2}, F x ∂canonicalRadialMass n b) ≤
      ENNReal.ofReal (Real.exp (-δ*((n+1:ℕ):ℝ)*(1+ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b-δ)) := by
  apply canonicalWeighted_mass_le n F hF
    (measurableSet_le measurable_const (continuous_norm.pow 2).measurable)
  intro x hx
  dsimp only [Set.mem_ofPred_eq,Pi.pow_apply] at hx
  have := mul_le_mul_of_nonneg_left hx hδ
  nlinarith

lemma canonicalWeighted_lower_tail (n : ℕ) (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F)
    (b ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫⁻ x in {x : RadialSpace n | ‖x‖^2 ≤ ((n+1:ℕ):ℝ)*(1-ε)}, F x ∂canonicalRadialMass n b) ≤
      ENNReal.ofReal (Real.exp (δ*((n+1:ℕ):ℝ)*(1-ε)/2)) *
        (∫⁻ x, F x ∂canonicalRadialMass n (b+δ)) := by
  apply canonicalWeighted_mass_le n F hF
    (measurableSet_le (continuous_norm.pow 2).measurable measurable_const)
  intro x hx
  dsimp only [Set.mem_ofPred_eq,Pi.pow_apply] at hx
  have := mul_le_mul_of_nonneg_left hx hδ
  nlinarith

def heatTilt (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  gaussianAverage s (expBCF d f * h) x / gaussianAverage s (expBCF d f) x

lemma heatTilt_zero (s : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    heatTilt s 0 f h x = gaussianAverage s h x := by
  simp [heatTilt,gaussianAverage,expBCF]

lemma gaussianAverage_affine (s : ℝ≥0) (f h : ℝ →ᵇ ℝ) (t x : ℝ) :
    gaussianAverage s (f+t • h : ℝ →ᵇ ℝ) x = gaussianAverage s f x + t * gaussianAverage s h x := by
  simp only [gaussianAverage,BoundedContinuousFunction.coe_add,
    BoundedContinuousFunction.coe_smul,Pi.add_apply,smul_eq_mul]
  rw [integral_add (gaussianAverage_integrable s f x)
    ((gaussianAverage_integrable s h x).const_mul t), integral_const_mul]

lemma gaussian_exp_affine_deriv (s : ℝ≥0) (d : ℝ) (f h : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianAverage s (expBCF d (f+u • h)) x)
      (d * gaussianAverage s (expBCF d (f+t • h) * h) x) t := by
  have hv : Measurable (fun z : ℝ => d*h (x+z)) := by fun_prop
  have hF : Measurable (fun z : ℝ => Real.exp (d*f (x+z))) := by fun_prop
  have hh := tilt_integral_deriv (gaussianReal 0 s) hv hF
    (mul_nonneg (abs_nonneg d) (norm_nonneg h)) (Real.exp_pos (|d| * ‖f‖)).le
    (fun z => by
      change |d*h (x+z)| ≤ |d| * ‖h‖
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm (x+z)) (abs_nonneg d))
    (fun z => exp_bcf_bound d f (x+z)) t
  convert! hh using 1
  · ext u
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [expBCF,BoundedContinuousFunction.mkOfBound_coe,
      ContinuousMap.coe_mk,BoundedContinuousFunction.coe_add,
      BoundedContinuousFunction.coe_smul,Pi.add_apply,smul_eq_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  · unfold gaussianAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [Pi.mul_apply,
      expBCF,BoundedContinuousFunction.mkOfBound_coe,ContinuousMap.coe_mk,
      BoundedContinuousFunction.coe_add,BoundedContinuousFunction.coe_smul,
      Pi.add_apply,smul_eq_mul]
    rw [show d*(f (x+z)+t*h (x+z))=t*(d*h (x+z))+d*f (x+z) by ring,Real.exp_add]
    ring

lemma heatLog_directional_deriv (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => heatLog s d (f+u • h) x)
      (heatTilt s d (f+t • h) h x) t := by
  by_cases hd : d = 0
  · subst d
    simp only [heatTilt_zero,heatLog,↓reduceIte,gaussianAverage_affine]
    convert! (hasDerivAt_const t (gaussianAverage s f x)).add
      ((hasDerivAt_id t).mul_const (gaussianAverage s h x)) using 1
    simp
  · have hh := ((gaussian_exp_affine_deriv s d f h t x).log
      (gaussianAverage_exp_pos s d (f+t • h) x).ne').const_mul (d:ℝ)⁻¹
    convert! hh using 1
    · simp only [heatLog,hd,↓reduceIte]
    · unfold heatTilt
      field_simp [NNReal.coe_ne_zero.mpr hd]

lemma gaussianAverage_add (s : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    gaussianAverage s (f+h : ℝ →ᵇ ℝ) x = gaussianAverage s f x + gaussianAverage s h x :=
  integral_add (gaussianAverage_integrable s f x) (gaussianAverage_integrable s h x)

lemma gaussianAverage_smul (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (a x : ℝ) :
    gaussianAverage s (a • f : ℝ →ᵇ ℝ) x = a * gaussianAverage s f x := by
  exact integral_const_mul _ _

lemma heatTilt_add (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (x : ℝ) :
    heatTilt s d f (h+k) x = heatTilt s d f h x + heatTilt s d f k x := by
  unfold heatTilt
  change gaussianAverage s (expBCF d f * (h+k) : ℝ →ᵇ ℝ) x / _ = _
  rw [mul_add,gaussianAverage_add,add_div]
  rfl

lemma heatTilt_smul (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (a x : ℝ) :
    heatTilt s d f (a • h) x = a * heatTilt s d f h x := by
  unfold heatTilt
  change gaussianAverage s (expBCF d f * (a • h) : ℝ →ᵇ ℝ) x / _ = _
  rw [mul_smul_comm,gaussianAverage_smul,mul_div_assoc]
  rfl

lemma heatTilt_const (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) (a x : ℝ) :
    heatTilt s d f (BoundedContinuousFunction.const ℝ a) x = a := by
  unfold heatTilt gaussianAverage
  simp only [Pi.mul_apply,BoundedContinuousFunction.const_apply]
  rw [integral_mul_const]
  exact mul_div_cancel_left₀ a (gaussianAverage_exp_pos s d f x).ne'

lemma heatTilt_nonneg (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (hh : ∀ x, 0 ≤ h x) (x : ℝ) :
    0 ≤ heatTilt s d f h x := by
  apply div_nonneg (integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (hh _))
    (gaussianAverage_exp_pos s d f x).le

lemma heatTilt_mono (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ)
    (hh : ∀ x, h x ≤ k x) (x : ℝ) : heatTilt s d f h x ≤ heatTilt s d f k x := by
  apply div_le_div_of_nonneg_right _ (gaussianAverage_exp_pos s d f x).le
  exact integral_mono (gaussianAverage_integrable s (expBCF d f*h) x)
    (gaussianAverage_integrable s (expBCF d f*k) x)
    (fun z => mul_le_mul_of_nonneg_left (hh _) (Real.exp_pos _).le)

lemma heatTilt_abs_le (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    |heatTilt s d f h x| ≤ ‖h‖ := by
  rw [abs_le]
  constructor
  · have hh := heatTilt_mono s d f (BoundedContinuousFunction.const ℝ (-‖h‖)) h
      (fun y => (abs_le.mp (h.norm_coe_le_norm y)).1) x
    simpa only [heatTilt_const] using hh
  · have hh := heatTilt_mono s d f h (BoundedContinuousFunction.const ℝ ‖h‖)
      (fun y => (abs_le.mp (h.norm_coe_le_norm y)).2) x
    simpa only [heatTilt_const] using hh

lemma heatTilt_sq (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    (heatTilt s d f h x)^2 ≤ heatTilt s d f (h^2) x := by
  let c := heatTilt s d f h x
  have hp := heatTilt_nonneg s d f ((h-BoundedContinuousFunction.const ℝ c)^2)
    (fun y => sq_nonneg _) x
  have he : (h-BoundedContinuousFunction.const ℝ c)^2 =
      h^2 + (-2*c) • h + BoundedContinuousFunction.const ℝ (c^2) := by
    ext y
    simp only [BoundedContinuousFunction.coe_pow,BoundedContinuousFunction.coe_sub,
      BoundedContinuousFunction.coe_add,BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.const_apply,Pi.pow_apply,Pi.sub_apply,Pi.add_apply,smul_eq_mul]
    ring
  rw [he,heatTilt_add,heatTilt_add,heatTilt_smul,heatTilt_const] at hp
  dsimp only [c] at hp
  nlinarith

lemma Jet3.heatLog_d1 (g : Jet3) (s d : ℝ≥0) (x : ℝ) :
    (g.heatLog s d).d1 x = heatTilt s d g.f g.d1 x := by
  by_cases hd : d = 0
  · subst d
    simp only [Jet3.heatLog,↓reduceDIte,heatTilt_zero]
    rfl
  · have he : (g.exp d).d1 = (d:ℝ) • (expBCF d g.f*g.d1) := rfl
    simp only [Jet3.heatLog,hd,↓reduceDIte,Jet3.heatLogPos]
    change (d:ℝ)⁻¹ * (SphericalPerceptronFreeEnergy.gaussianAverage s (g.exp d).d1 x *
      (SphericalPerceptronFreeEnergy.gaussianAverage s (expBCF d g.f) x)⁻¹) = _
    rw [he,SphericalPerceptronFreeEnergy.gaussianAverage_smul]
    unfold heatTilt
    field_simp [NNReal.coe_ne_zero.mpr hd]
    rfl

lemma Jet3.heatLog_d1_sq_le (g : Jet3) (s d : ℝ≥0) (x : ℝ) :
    ((g.heatLog s d).d1 x)^2 ≤ heatTilt s d g.f (g.d1^2) x := by
  rw [g.heatLog_d1]
  exact heatTilt_sq s d g.f g.d1 x

lemma gaussian_exp_affine_mul_deriv (s : ℝ≥0) (d : ℝ) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => gaussianAverage s (expBCF d (f+u • h)*k : ℝ →ᵇ ℝ) x)
      (d * gaussianAverage s (expBCF d (f+t • h) * (h*k) : ℝ →ᵇ ℝ) x) t := by
  have hv : Measurable (fun z : ℝ => d*h (x+z)) := by fun_prop
  have hF : Measurable (fun z : ℝ => Real.exp (d*f (x+z))*k (x+z)) := by fun_prop
  have hh := tilt_integral_deriv (gaussianReal 0 s) hv hF
    (mul_nonneg (abs_nonneg d) (norm_nonneg h))
    (mul_nonneg (Real.exp_pos (|d| * ‖f‖)).le (norm_nonneg k))
    (fun z => by
      change |d*h (x+z)| ≤ |d| * ‖h‖
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm (x+z)) (abs_nonneg d))
    (fun z => by
      rw [abs_mul]
      exact mul_le_mul (exp_bcf_bound d f (x+z)) (k.norm_coe_le_norm (x+z))
        (abs_nonneg _) (Real.exp_pos _).le) t
  convert! hh using 1
  · ext u
    apply integral_congr_ae
    filter_upwards [] with z
    change Real.exp (d*(f (x+z)+u*h (x+z)))*k (x+z) = _
    rw [show d*(f (x+z)+u*h (x+z))=u*(d*h (x+z))+d*f (x+z) by ring,Real.exp_add]
    ring
  · unfold gaussianAverage
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    change d*(Real.exp (d*(f (x+z)+t*h (x+z)))*(h (x+z)*k (x+z))) = _
    rw [show d*(f (x+z)+t*h (x+z))=t*(d*h (x+z))+d*f (x+z) by ring,Real.exp_add]
    ring

lemma heatTilt_directional_deriv (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    HasDerivAt (fun u : ℝ => heatTilt s d (f+u • h) k x)
      ((d:ℝ)*(heatTilt s d (f+t • h) (h*k) x -
        heatTilt s d (f+t • h) h x * heatTilt s d (f+t • h) k x)) t := by
  have hh := (gaussian_exp_affine_mul_deriv s d f h k t x).div
    (gaussian_exp_affine_deriv s d f h t x) (gaussianAverage_exp_pos s d (f+t • h) x).ne'
  convert! hh using 1
  unfold heatTilt
  simp only [← BoundedContinuousFunction.coe_mul]
  field_simp

lemma heatTilt_directional_bound (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    |(d:ℝ)*(heatTilt s d (f+t • h) (h*k) x -
        heatTilt s d (f+t • h) h x * heatTilt s d (f+t • h) k x)| ≤
      2*(d:ℝ)*‖h‖*‖k‖ := by
  rw [abs_mul,abs_of_nonneg d.coe_nonneg]
  calc
    _ ≤ (d:ℝ)*(|heatTilt s d (f+t • h) (h*k) x| +
        |heatTilt s d (f+t • h) h x * heatTilt s d (f+t • h) k x|) := by
      gcongr; exact abs_sub _ _
    _ ≤ (d:ℝ)*(‖h*k‖ + ‖h‖*‖k‖) := by
      rw [abs_mul]
      gcongr
      · exact heatTilt_abs_le s d _ _ x
      · exact heatTilt_abs_le s d _ _ x
      · exact heatTilt_abs_le s d _ _ x
    _ ≤ 2*(d:ℝ)*‖h‖*‖k‖ := by
      nlinarith [mul_le_mul_of_nonneg_left (norm_mul_le h k) d.coe_nonneg]

lemma heatTilt_affine_sub_bound (s d : ℝ≥0) (f h k : ℝ →ᵇ ℝ) (t x : ℝ) :
    |heatTilt s d (f+t • h) k x - heatTilt s d f k x| ≤
      2*(d:ℝ)*‖h‖*‖k‖*|t| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (fun u _ => (heatTilt_directional_deriv s d f h k u x).hasDerivWithinAt)
    (fun u _ => heatTilt_directional_bound s d f h k u x) convex_univ
    (mem_univ (0:ℝ)) (mem_univ t)
  simpa only [zero_smul,add_zero,sub_zero,Real.norm_eq_abs] using hh

lemma heatLog_terminal_quadratic_error (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    |heatLog s d (f+h) x - heatLog s d f x - heatTilt s d f h x| ≤
      2*(d:ℝ)*‖h‖^2 := by
  have hd (u : ℝ) : HasDerivAt
      (fun t => heatLog s d (f+t • h) x - heatLog s d f x - t*heatTilt s d f h x)
      (heatTilt s d (f+u • h) h x - heatTilt s d f h x) u := by
    convert! ((heatLog_directional_deriv s d f h u x).sub_const (heatLog s d f x)).sub
      ((hasDerivAt_id u).mul_const (heatTilt s d f h x)) using 1
    simp
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun u _ => (hd u).hasDerivWithinAt) (fun u hu => show
      ‖heatTilt s d (f+u • h) h x - heatTilt s d f h x‖ ≤ 2*(d:ℝ)*‖h‖^2 from by
        calc
          _ ≤ 2*(d:ℝ)*‖h‖*‖h‖*|u| := heatTilt_affine_sub_bound s d f h h u x
          _ ≤ 2*(d:ℝ)*‖h‖^2 := by
            rw [abs_of_nonneg hu.1]
            nlinarith [mul_nonneg (show 0 ≤ 2*(d:ℝ)*‖h‖^2 by positivity) (sub_nonneg.mpr hu.2.le)])
  simpa only [zero_smul,one_smul,add_zero,zero_mul,one_mul,sub_self,sub_zero,
    Real.norm_eq_abs] using hh

lemma heatTilt_continuous (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) : Continuous (heatTilt s d f h) :=
  (gaussianAverage_continuous s (expBCF d f*h)).div
    (gaussianAverage_continuous s (expBCF d f)) (fun x => (gaussianAverage_exp_pos s d f x).ne')

def heatTiltBCF (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨heatTilt s d f h,heatTilt_continuous s d f h⟩
    (2*‖h‖) (fun x y => by
      change |heatTilt s d f h x - heatTilt s d f h y| ≤ 2*‖h‖
      exact (abs_sub _ _).trans (by linarith [heatTilt_abs_le s d f h x,heatTilt_abs_le s d f h y]))

@[simp] lemma heatTiltBCF_apply (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) (x : ℝ) :
    heatTiltBCF s d f h x = heatTilt s d f h x := rfl

lemma heatTiltBCF_norm_le (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) : ‖heatTiltBCF s d f h‖ ≤ ‖h‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg h)).mpr (heatTilt_abs_le s d f h)

def heatTiltCLM (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := heatTiltBCF s d f
      map_add' := fun h k => by ext x; exact heatTilt_add s d f h k x
      map_smul' := fun a h => by ext x; exact heatTilt_smul s d f h a x }
    1 (fun h => by
      change ‖heatTiltBCF s d f h‖ ≤ 1*‖h‖
      simpa only [one_mul] using heatTiltBCF_norm_le s d f h)

lemma heatLogBCF_terminal_quadratic_error (s d : ℝ≥0) (f h : ℝ →ᵇ ℝ) :
    ‖heatLogBCF s d (f+h)-heatLogBCF s d f-heatTiltCLM s d f h‖ ≤ 2*(d:ℝ)*‖h‖^2 :=
  (BoundedContinuousFunction.norm_le (by positivity)).mpr (heatLog_terminal_quadratic_error s d f h)

lemma heatLogBCF_hasFDerivAt (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    HasFDerivAt (heatLogBCF s d) (heatTiltCLM s d f) f := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have he : ∀ᶠ h : (ℝ →ᵇ ℝ) in 𝓝 0, ‖h‖ < ε/(2*(d:ℝ)+1) :=
    by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ →ᵇ ℝ)
        (show 0 < ε/(2*(d:ℝ)+1) by positivity)] with h hh
      simpa only [Metric.mem_ball,dist_zero_right] using hh
  filter_upwards [he] with h hh
  calc
    _ ≤ 2*(d:ℝ)*‖h‖^2 := heatLogBCF_terminal_quadratic_error s d f h
    _ ≤ ε*‖h‖ := by
      have hb : ‖h‖*(2*(d:ℝ)+1) < ε := (lt_div_iff₀ (by positivity)).mp hh
      nlinarith [norm_nonneg h,mul_nonneg (norm_nonneg h) (sub_nonneg.mpr hb.le)]

def shiftBCF (f : ℝ →ᵇ ℝ) (a : ℝ) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨fun x => x+a,by fun_prop⟩

@[simp] lemma shiftBCF_apply (f : ℝ →ᵇ ℝ) (a x : ℝ) : shiftBCF f a x = f (x+a) := rfl

lemma shiftBCF_norm_le (f : ℝ →ᵇ ℝ) (a : ℝ) : ‖shiftBCF f a‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (fun x => f.norm_coe_le_norm (x+a))

lemma shiftBCF_lipschitz (f f' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x) :
    LipschitzWith ‖f'‖₊ (shiftBCF f) := by
  have hl := lipschitzWith_of_nnnorm_deriv_le (C := ‖f'‖₊) (fun x => (hf x).differentiableAt) (fun x => by
    rw [(hf x).deriv]
    exact_mod_cast f'.norm_coe_le_norm x)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change |f (x+a)-f (x+b)| ≤ _
  simpa only [Real.dist_eq,add_sub_add_left_eq_sub,coe_nnnorm] using hl.dist_le_mul (x+a) (x+b)

lemma shiftBCF_Jet3_hasDerivAt (g : Jet3) (a : ℝ) :
    HasDerivAt (shiftBCF g.f) (shiftBCF g.d1 a) a := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have he : ∀ᶠ h : ℝ in 𝓝 0, |h| < ε/(‖g.d2‖+1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (show 0 < ε/(‖g.d2‖+1) by positivity)] with h hh
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh
  filter_upwards [he] with h hh
  have hb : ‖shiftBCF g.f (a+h)-shiftBCF g.f a-h • shiftBCF g.d1 a‖ ≤ ‖g.d2‖*h^2/2 := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    have ht := first_order_taylor_bound (g.contDiff.of_le (by norm_num)) ‖g.d2‖
      (fun y => by rw [g.deriv2_eq]; exact g.d2.norm_coe_le_norm y) (x+a) (x+(a+h))
    rw [g.deriv_eq] at ht
    convert! ht using 1 <;> simp [shiftBCF,add_comm,add_left_comm,mul_comm]
  calc
    _ ≤ ‖g.d2‖*h^2/2 := hb
    _ ≤ ε*‖h‖ := by
      have ht : |h| * (‖g.d2‖+1) < ε := (lt_div_iff₀ (by positivity)).mp hh
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs h,abs_nonneg h,norm_nonneg g.d2,
        mul_nonneg (abs_nonneg h) (sub_nonneg.mpr ht.le)]

end SphericalPerceptronFreeEnergy

end

end OAI

import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ReverseMoments
import OAI.Probability.SLEGauge.BrownianShifts

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
open Filter Topology
noncomputable section
open Complex Real Set Filter
open scoped Topology
noncomputable section
open scoped Topology
open MeasureTheory
noncomputable section
open Set Filter Real
open scoped Topology
open Set MeasureTheory ProbabilityTheory Topology Function Filter
open scoped NNReal ENNReal ContinuousMapZero
noncomputable section
namespace SLEExactGauge.LiteralTrace
open ReverseDerivative
lemma forward_integral_eq_reverse {κ y T : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hT : 0 ≤ T)
    (b : Driver) :
    (∫ u in (0:ℝ)..T, -(a κ:ℂ)/
      (flow κ b (reversedCurve κ y T b T+driverValue b T) (timeClip T u)-driverValue b (timeClip T u))^2) =
        -(∫ s in (0:ℝ)..T, reverseCoeff κ y T b s) := by
  have hf := reverse_reparam_solution hκ hy hT b
  have hrev (u : ℝ) (hu : u ∈ Icc 0 T) : T-u ∈ Icc 0 T := by constructor <;> linarith [hu.1,hu.2]
  have heq (u : ℝ) (hu : u ∈ Icc 0 T) :
      -(a κ:ℂ)/(flow κ b (reversedCurve κ y T b T+driverValue b T) (timeClip T u)-driverValue b (timeClip T u))^2 =
        -reverseCoeff κ y T b (T-u) := by
    rw [timeClip_eq hu,hf.flow_eqOn hu]
    have hβ := BrownianRestart.backward_before (hrev u hu) b
    simp only [sub_sub_cancel] at hβ
    simp only [reverseCoeff,hβ,driverValue,Complex.ofReal_sub]
    have hden : reversedCurve κ y T b (T-u)+(b T.toNNReal:ℂ)-b u.toNNReal =
        reversedCurve κ y T b (T-u)-((b u.toNNReal:ℂ)-b T.toNNReal) := by ring
    rw [hden]
    simp only [div_eq_mul_inv,inv_pow,neg_mul]
  calc
    _ = (∫ u in (0:ℝ)..T, -reverseCoeff κ y T b (T-u)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact heq u (by simpa only [uIcc_of_le hT] using hu)
    _ = -(∫ u in (0:ℝ)..T, reverseCoeff κ y T b (T-u)) := intervalIntegral.integral_neg
    _ = -(∫ s in (0:ℝ)..T, reverseCoeff κ y T b s) := by
      rw [intervalIntegral.integral_comp_sub_left]
      simp only [sub_self,sub_zero]

 

theorem inverseFlow_deriv_norm_eq_reverse {κ y T : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hT : 0 ≤ T)
    (b : Driver) : ‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖ =
      Real.exp ((reversedState κ y T b T).2.2) := by
  have hw : 0 < ((driverValue b T:ℂ)+y*Complex.I).im := by simpa using hy
  have hd := (inverseFlow_hasStrictDerivAt hκ b hT hw).hasDerivAt.deriv
  rw [hd,inverseFlow_eq_reversedCurve hκ hy hT b,
    (flow_hasDerivAt_initial hT (reverse_reparam_solution hκ hy hT b).surviving).deriv,
    forward_integral_eq_reverse hκ hy hT b,norm_inv,Complex.norm_exp,Complex.neg_re,
    ← Real.exp_neg,neg_neg,reversed_log_eq_integral hκ hy hT b]
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace
open ReverseDerivative MeasureTheory ProbabilityTheory

lemma measurable_reverse_log (a y T : ℝ) (hy : 0 < y) :
    Measurable (fun b : Driver =>
      (ReverseDerivative.reverseFlow a (y/4) (T+y^2) y b T).2.2) :=
  (ReverseDerivative.measurable_driven (by positivity : 0 < y/4)
    a (ReverseDerivative.initial (T+y^2) y) T).fst.snd.snd

lemma measurable_inverse_deriv_norm {κ y T : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hT : 0 ≤ T) :
    Measurable (fun b : Driver => ‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖) := by
  simp_rw [inverseFlow_deriv_norm_eq_reverse hκ hy hT]
  exact ((measurable_reverse_log (a κ) y T hy).comp (BrownianRestart.measurable_backward T.toNNReal)).exp

 

theorem inverse_deriv_moment {κ y T : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hy : 0 < y) (hT : 0 ≤ T) {W : WienerLaw} (hW : IsWiener W) :
    (∫⁻ b : Driver, ENNReal.ofReal
      (‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖^(lambda (a κ))) ∂W) ≤
      ENNReal.ofReal ((3*y^2/(T+3*y^2))^(zeta (a κ)/2)) := by
  have ha : 1/4 < a κ := by unfold a; apply (lt_div_iff₀ hκ).mpr; linarith
  let F := fun b : Driver => ENNReal.ofReal (Real.exp
    (lambda (a κ)*(ReverseDerivative.reverseFlow (a κ) (y/4) (T+y^2) y b T).2.2))
  have mF : Measurable F :=
    (measurable_const.mul (measurable_reverse_log (a κ) y T hy)).exp.ennreal_ofReal
  have hid (b : Driver) :
      ENNReal.ofReal (‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖^(lambda (a κ))) =
        F (BrownianRestart.backward T.toNNReal b) := by
    rw [inverseFlow_deriv_norm_eq_reverse hκ hy hT,
      Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,mul_comm]
    rfl
  simp_rw [hid]
  rw [← lintegral_map mF (BrownianRestart.measurable_backward T.toNNReal),
    BrownianRestart.backward_preserves_law hW]
  exact ReverseDerivative.reverse_logderiv_moment ha hy hT hW
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open ReverseDerivative MeasureTheory ProbabilityTheory

lemma lambda_gt_one {a : ℝ} (ha : 0 < a) : 1 < lambda a := by
  unfold lambda
  have hh : 0 < 3/(16*a) := by positivity
  linarith

lemma inverse_deriv_first_moment {κ y T : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hy : 0 < y) (hT : 0 ≤ T) {W : WienerLaw} (hW : IsWiener W) :
    (∫⁻ b : Driver, ENNReal.ofReal ‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖ ∂W) ≤ 2 := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have ha : 1/4 < a κ := by unfold a; apply (lt_div_iff₀ hκ).mpr; linarith
  have hl := lambda_gt_one (show 0 < a κ by linarith)
  have hp (x : ℝ) (hx : 0 ≤ x) : x ≤ 1+x^(lambda (a κ)) := by
    by_cases h : x ≤ 1
    · exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg hx _))
    · have he := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hl.le
      simpa only [Real.rpow_one] using he.trans (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1))
  calc
    _ ≤ ∫⁻ b : Driver, (1+ENNReal.ofReal (‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖^(lambda (a κ)))) ∂W := by
      apply lintegral_mono
      intro b
      dsimp only
      rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)]
      exact ENNReal.ofReal_le_ofReal (hp _ (norm_nonneg _))
    _ = 1+(∫⁻ b : Driver, ENNReal.ofReal (‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖^(lambda (a κ))) ∂W) := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ 1+ENNReal.ofReal ((3*y^2/(T+3*y^2))^(zeta (a κ)/2)) :=
      add_le_add le_rfl (inverse_deriv_moment hκ hκ8 hy hT hW)
    _ ≤ 2 := by
      have hr : 3*y^2/(T+3*y^2) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 3*y^2/(T+3*y^2)) hr
        (by linarith [(parameters ha).1] : 0 ≤ zeta (a κ)/2)
      simp only [Real.one_rpow] at hh
      have hh' : ENNReal.ofReal ((3*y^2/(T+3*y^2))^(zeta (a κ)/2)) ≤ 1 := by
        simpa using ENNReal.ofReal_le_ofReal hh
      calc _ ≤ 1+1 := add_le_add le_rfl hh'
           _ = 2 := by norm_num

 
def radialCoeff (κ : ℝ) (b : Driver) (T y : ℝ) : ℂ :=
  if 0 < y then deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)*Complex.I else 0

lemma continuousOn_radialCoeff {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (b : Driver) :
    ContinuousOn (radialCoeff κ b T) (Ioi 0) := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hc := (((flow_conformal_bijection hκ b hT).2.2.2).analyticOnNhd hopen).deriv.continuousOn
  have hline : Continuous (fun y : ℝ => (driverValue b T:ℂ)+y*Complex.I) := by fun_prop
  have hh := (hc.comp hline.continuousOn (show MapsTo (fun y : ℝ => (driverValue b T:ℂ)+y*Complex.I) (Ioi 0) {w : ℂ | 0 < w.im} from by intro y hy; simpa using hy)).mul (continuousOn_const (c := Complex.I))
  apply hh.congr
  intro y hy
  rw [radialCoeff,ite_eq_left (show 0 < y from hy)]
  rfl

lemma measurable_positive_radial_norm {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) :
    Measurable (fun p : (Ioi (0:ℝ)) × Driver =>
      ‖deriv (inverseFlow κ p.2 T) (driverValue p.2 T+(p.1:ℝ)*Complex.I)‖) := by
  exact measurable_uncurry_of_continuous_of_measurable
    (u := fun (y : Ioi (0:ℝ)) (b : Driver) => ‖deriv (inverseFlow κ b T) (driverValue b T+(y:ℝ)*Complex.I)‖) (by
    intro b
    have hh := (continuousOn_radialCoeff hκ hT b).norm.domRestrict
    have he : ((Ioi (0:ℝ)).domRestrict (fun y => ‖radialCoeff κ b T y‖)) =
        (fun y : Ioi (0:ℝ) => ‖deriv (inverseFlow κ b T) (driverValue b T+(y:ℝ)*Complex.I)‖) := by
      funext y
      change ‖radialCoeff κ b T y‖ = _
      rw [radialCoeff,ite_eq_left (show 0 < (y:ℝ) from y.property),norm_mul,Complex.norm_I,mul_one]
    rwa [he] at hh) (by
    intro y
    exact measurable_inverse_deriv_norm hκ y.property hT)

lemma measurable_radial_norm {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) :
    Measurable (fun p : ℝ × Driver => ‖radialCoeff κ p.2 T p.1‖) := by
  have hm := measurable_positive_radial_norm hκ hT
  apply measurable_of_restrict_of_restrict_compl (s := {p : ℝ × Driver | 0 < p.1})
    (measurableSet_lt measurable_const measurable_fst)
  · have mm : Measurable (fun p : {p : ℝ × Driver | 0 < p.1} =>
        ((⟨p.val.1,p.property⟩ : Ioi (0:ℝ)),p.val.2)) :=
      (measurable_subtype_coe.fst.subtype_mk).prodMk measurable_subtype_coe.snd
    have he : ({p : ℝ × Driver | 0 < p.1}.domRestrict
        (fun p : ℝ × Driver => ‖radialCoeff κ p.2 T p.1‖)) =
        (fun p : {p : ℝ × Driver | 0 < p.1} =>
          ‖deriv (inverseFlow κ p.val.2 T) (driverValue p.val.2 T+p.val.1*Complex.I)‖) := by
      funext p
      change ‖radialCoeff κ p.val.2 T p.val.1‖ = _
      rw [radialCoeff,ite_eq_left (show 0 < p.val.1 from p.property),norm_mul,Complex.norm_I,mul_one]
    rw [he]
    have hh := hm.comp mm
    change Measurable (fun p : {p : ℝ × Driver | 0 < p.1} =>
      ‖deriv (inverseFlow κ p.val.2 T) (driverValue p.val.2 T+p.val.1*Complex.I)‖) at hh
    exact hh
  · have he : ({p : ℝ × Driver | 0 < p.1}ᶜ.domRestrict
        (fun p : ℝ × Driver => ‖radialCoeff κ p.2 T p.1‖)) =
        (fun _ : ↥({p : ℝ × Driver | 0 < p.1}ᶜ) => (0:ℝ)) := by
      funext p
      change ‖radialCoeff κ p.val.2 T p.val.1‖ = 0
      rw [radialCoeff,ite_eq_right (show ¬0 < p.val.1 from p.property),norm_zero]
    rw [he]
    exact measurable_const

lemma radial_length_ae_finite {κ T : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hT : 0 ≤ T) {W : WienerLaw} (hW : IsWiener W) :
    ∀ᵐ b ∂W, (∫⁻ y in Icc (0:ℝ) 1, ENNReal.ofReal ‖radialCoeff κ b T y‖) < (∞:ℝ≥0∞) := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let F := fun b : Driver => ∫⁻ y in Icc (0:ℝ) 1, ENNReal.ofReal ‖radialCoeff κ b T y‖
  have hm := (measurable_radial_norm hκ hT).ennreal_ofReal
  have mF : Measurable F := (hm.comp measurable_swap).lintegral_prod_right'
  apply ae_lt_top mF
  have hs : (∫⁻ b, F b ∂W) ≤ 2 := by
    rw [show (∫⁻ b, F b ∂W) = ∫⁻ y in Icc (0:ℝ) 1, ∫⁻ b, ENNReal.ofReal ‖radialCoeff κ b T y‖ ∂W from
      lintegral_lintegral_swap (hm.comp measurable_swap).aemeasurable]
    calc
      _ ≤ ∫⁻ y in Icc (0:ℝ) 1, (2:ℝ≥0∞) := by
        apply lintegral_mono
        intro y
        by_cases hy : 0 < y
        · simpa only [radialCoeff,ite_eq_left hy,norm_mul,Complex.norm_I,mul_one] using
            inverse_deriv_first_moment hκ hκ8 hy hT hW
        · simp only [radialCoeff,ite_eq_right hy,norm_zero,ENNReal.ofReal_zero,lintegral_zero]
          exact bot_le
      _ = 2 := by simp
  exact ne_top_of_le_ne_top (by norm_num) hs
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open MeasureTheory

lemma measurable_radialCoeff {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (b : Driver) :
    Measurable (radialCoeff κ b T) := by
  apply measurable_of_restrict_of_restrict_compl (s := Ioi (0:ℝ)) measurableSet_Ioi
  · exact (continuousOn_radialCoeff hκ hT b).domRestrict.measurable
  · have he : ((Ioi (0:ℝ))ᶜ.domRestrict (radialCoeff κ b T)) =
        (fun _ : ↥((Ioi (0:ℝ))ᶜ) => (0:ℂ)) := by
      funext y
      change radialCoeff κ b T y.val = 0
      rw [radialCoeff,ite_eq_right (show ¬0 < y.val from y.property)]
    rw [he]
    exact measurable_const

lemma hasDerivAt_radial {κ T y : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (hy : 0 < y) (b : Driver) :
    HasDerivAt (fun y : ℝ => inverseFlow κ b T (driverValue b T+y*Complex.I))
      (radialCoeff κ b T y) y := by
  have hw : 0 < ((driverValue b T:ℂ)+y*Complex.I).im := by simpa using hy
  have hf := (inverseFlow_hasStrictDerivAt hκ b hT hw).hasDerivAt.differentiableAt.hasDerivAt
  have hl : HasDerivAt (fun z : ℂ => (driverValue b T:ℂ)+z*Complex.I) Complex.I (y:ℂ) := by
    convert! (hasDerivAt_const (y:ℂ) (driverValue b T:ℂ)).add ((hasDerivAt_id (y:ℂ)).mul_const Complex.I) using 1; simp
  convert! (hf.comp (y:ℂ) hl).comp_ofReal using 1; simp only [radialCoeff,ite_eq_left hy]

lemma radial_limit_of_integrable {κ T : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (b : Driver)
    (hi : IntegrableOn (radialCoeff κ b T) (Icc (0:ℝ) 1)) :
    ∃ z : ℂ, Tendsto (fun y : ℝ => inverseFlow κ b T (driverValue b T+y*Complex.I))
      (𝓝[>] 0) (𝓝 z) := by
  let f := fun y : ℝ => inverseFlow κ b T (driverValue b T+y*Complex.I)
  let v := fun y : ℝ => radialCoeff κ b T y
  have hi' : IntegrableOn v (uIcc (0:ℝ) 1) := by simpa only [uIcc_of_le zero_le_one] using hi
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hi'
  have hevent : ∀ᶠ y : ℝ in 𝓝[>] 0, y ∈ Ioc (0:ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 from nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))] with y hy hy1
    exact ⟨hy,hy1.le⟩
  have hmap : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝[uIcc (0:ℝ) 1] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id'.mpr nhdsWithin_le_nhds,?_⟩
    filter_upwards [hevent] with y hy
    simpa only [uIcc_of_le zero_le_one] using (show y ∈ Icc (0:ℝ) 1 from ⟨hy.1.le,hy.2⟩)
  have hlim := ((hcont 0 left_mem_uIcc).tendsto.comp hmap).const_sub (f 1)
  refine ⟨f 1-(∫ u in (0:ℝ)..1, v u),hlim.congr' ?_⟩
  filter_upwards [hevent] with y hy
  have hd (u : ℝ) (hu : u ∈ uIcc y 1) : HasDerivAt f (v u) u := by
    rw [uIcc_of_le hy.2] at hu
    exact hasDerivAt_radial hκ hT (hy.1.trans_le hu.1) b
  have hint : IntervalIntegrable v volume y 1 := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hy.2] using
      (hi.mono_set (show Icc y 1 ⊆ Icc (0:ℝ) 1 from Icc_subset_Icc hy.1.le le_rfl))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [Function.comp_apply]
  rw [he]
  exact sub_sub_cancel _ _

 

theorem radial_limit_ae {κ T : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hT : 0 ≤ T) {W : WienerLaw} (hW : IsWiener W) :
    ∀ᵐ b ∂W, ∃ z : ℂ,
      Tendsto (fun y : ℝ => inverseFlow κ b T (driverValue b T+y*Complex.I)) (𝓝[>] 0) (𝓝 z) := by
  filter_upwards [radial_length_ae_finite hκ hκ8 hT hW] with b hb
  apply radial_limit_of_integrable hκ hT b
  exact ⟨(measurable_radialCoeff hκ hT b).aestronglyMeasurable,
    (hasFiniteIntegral_iff_norm _).mpr hb⟩

 

theorem trace_limit_countable {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {W : WienerLaw} (hW : IsWiener W) (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) :
    ∀ᵐ b ∂W, ∀ n : ℕ,
      Tendsto (fun y : ℝ => inverseFlow κ b (κ*t n) (driverValue b (κ*t n)+y*Complex.I))
        (𝓝[>] 0) (𝓝 (trace κ b (t n))) := by
  have hh := ae_all_iff.mpr (fun n => radial_limit_ae hκ hκ8 (mul_nonneg hκ.le (ht n)) hW)
  filter_upwards [hh] with b hb
  intro n
  obtain ⟨z,hz⟩ := hb n
  have he : trace κ b (t n) = z := by
    exact hz.limUnder_eq
  rwa [he]
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open ReverseDerivative MeasureTheory

 

def traceBeta (κ : ℝ) : ℝ :=
  (lambda (a κ)+zeta (a κ)-2)/(2*lambda (a κ))

def traceEta (κ : ℝ) : ℝ := (lambda (a κ)+zeta (a κ)-2)/2

lemma trace_exponents {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < traceBeta κ ∧ traceBeta κ < 1 ∧ 0 < traceEta κ ∧
      zeta (a κ)-(traceBeta κ-1)*lambda (a κ) = 2+traceEta κ := by
  have ha : 1/4 < a κ := by unfold a; apply (lt_div_iff₀ hκ).mpr; linarith
  have hp := parameters ha
  have hsum : 0 < lambda (a κ)+zeta (a κ)-2 := by linarith [hp.2.2.1]
  have hden : 0 < 2*lambda (a κ) := by linarith [hp.2.1]
  have hlt : zeta (a κ) < lambda (a κ)+2 := by
    unfold lambda zeta
    have : 0 < a κ := by linarith
    have h1 : 0 ≤ 1/(16*a κ) := by positivity
    have h3 : 0 ≤ 3/(16*a κ) := by positivity
    linarith
  refine ⟨div_pos hsum hden, (div_lt_one hden).mpr (by linarith),div_pos hsum (by norm_num),?_⟩
  unfold traceBeta traceEta
  field_simp [ne_of_gt hp.2.1]
  ring

lemma inverse_deriv_moment_away {κ y T δ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hy : 0 < y) (hδ : 0 < δ) (hT : δ ≤ T) {W : WienerLaw} (hW : IsWiener W) :
    (∫⁻ b : Driver, ENNReal.ofReal
      (‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖^(lambda (a κ))) ∂W) ≤
      ENNReal.ofReal ((3/δ)^(zeta (a κ)/2)*y^(zeta (a κ))) := by
  have ha : 1/4 < a κ := by unfold a; apply (lt_div_iff₀ hκ).mpr; linarith
  have hz := (parameters ha).1
  have hT0 : 0 ≤ T := hδ.le.trans hT
  apply (inverse_deriv_moment hκ hκ8 hy (hδ.le.trans hT) hW).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((3/δ)*y^2)^(zeta (a κ)/2) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      calc
        _ ≤ 3*y^2/δ := div_le_div_of_nonneg_left (by positivity) hδ (by nlinarith)
        _ = (3/δ)*y^2 := by ring
    _ = (3/δ)^(zeta (a κ)/2)*y^(zeta (a κ)) := by
      rw [Real.mul_rpow (by positivity) (sq_nonneg y),
        ← Real.rpow_natCast_mul hy.le 2 (zeta (a κ)/2)]
      congr 1
      congr 1
      norm_num
      ring

lemma inverse_deriv_tail_away {κ y T δ K : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hy : 0 < y) (hδ : 0 < δ) (hT : δ ≤ T) (hK : 0 < K)
    {W : WienerLaw} (hW : IsWiener W) :
    W {b : Driver | K ≤ ‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖} ≤
      ENNReal.ofReal (((3/δ)^(zeta (a κ)/2)*y^(zeta (a κ)))/K^(lambda (a κ))) := by
  have ha : 1/4 < a κ := by unfold a; apply (lt_div_iff₀ hκ).mpr; linarith
  have hl := (parameters ha).2.1
  have hm := ((measurable_inverse_deriv_norm hκ hy (hδ.le.trans hT)).pow_const
    (lambda (a κ))).ennreal_ofReal
  have hKP : 0 < K^(lambda (a κ)) := Real.rpow_pos_of_pos hK _
  calc
    _ ≤ W {b : Driver | ENNReal.ofReal (K^(lambda (a κ))) ≤ ENNReal.ofReal
        (‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖^(lambda (a κ)))} := by
      apply measure_mono
      intro b hb
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hK.le hb hl.le)
    _ ≤ (∫⁻ b : Driver, ENNReal.ofReal
        (‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖^(lambda (a κ))) ∂W)/
        ENNReal.ofReal (K^(lambda (a κ))) :=
      meas_ge_le_lintegral_div hm.aemeasurable (ne_of_gt (ENNReal.ofReal_pos.mpr hKP)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((3/δ)^(zeta (a κ)/2)*y^(zeta (a κ)))/
        ENNReal.ofReal (K^(lambda (a κ))) := by
      exact ENNReal.div_le_div_right (inverse_deriv_moment_away hκ hκ8 hy hδ hT hW) _
    _ = ENNReal.ofReal (((3/δ)^(zeta (a κ)/2)*y^(zeta (a κ)))/K^(lambda (a κ))) :=
      (ENNReal.ofReal_div_of_pos hKP).symm

lemma inverse_deriv_beta_tail {κ y T δ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (hy : 0 < y) (hδ : 0 < δ) (hT : δ ≤ T) {W : WienerLaw} (hW : IsWiener W) :
    W {b : Driver | y^(traceBeta κ-1) ≤
      ‖deriv (inverseFlow κ b T) (driverValue b T+y*Complex.I)‖} ≤
      ENNReal.ofReal ((3/δ)^(zeta (a κ)/2)*y^(2+traceEta κ)) := by
  have hp := trace_exponents hκ hκ8
  have he : ((3/δ)^(zeta (a κ)/2)*y^(zeta (a κ)))/(y^(traceBeta κ-1))^(lambda (a κ)) =
      (3/δ)^(zeta (a κ)/2)*y^(2+traceEta κ) := by
    rw [← Real.rpow_mul hy.le, mul_div_assoc, ← Real.rpow_sub hy,
      hp.2.2.2]
  simpa only [he] using (inverse_deriv_tail_away hκ hκ8 hy hδ hT
    (Real.rpow_pos_of_pos hy (traceBeta κ-1)) hW)
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open ReverseDerivative MeasureTheory

lemma lintegral_pow_le_mass {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, f x ∂μ)^p ≤ (μ univ)^(p-1)*(∫⁻ x, (f x)^p ∂μ) := by
  have hp0 : 0 < p := by linarith
  let q := p/(p-1)
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp,?_⟩
    dsimp [q]
    field_simp
    ring
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf
    (aemeasurable_const (b := (1:ℝ≥0∞)))
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at hh
  have hh' := ENNReal.rpow_le_rpow hh hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,← ENNReal.rpow_mul,
    one_div_mul_cancel (ne_of_gt hp0),ENNReal.rpow_one,← ENNReal.rpow_mul] at hh'
  have he : (1/q)*p = p-1 := by dsimp [q]; field_simp
  rw [he,mul_comm] at hh'
  exact hh'

 
def radialLength (κ : ℝ) (b : Driver) (T y : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioc (0:ℝ) y, ENNReal.ofReal ‖radialCoeff κ b T u‖

end SLEExactGauge.LiteralTrace
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

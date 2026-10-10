import Mathlib
import OAI.Probability.SKGap.Localization.ScalarFixedPointJoined

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
namespace SKGap

theorem entropy_fenchel {r : ℝ} (hr : 0 ≤ r) (v : ℝ) :
    r * v ≤ klFun r + exp v - 1 := by
  rcases hr.eq_or_lt with rfl | hr
  · simpa [klFun] using (exp_pos v).le
  · have h := mul_le_mul_of_nonneg_left (add_one_le_exp (v - log r)) hr.le
    rw [exp_sub, exp_log hr, mul_div_cancel₀ _ hr.ne'] at h
    unfold klFun
    nlinarith

theorem entropy_variational {α : Type*} [MeasurableSpace α]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hD : klDiv P Q ≠ ⊤) {f : α → ℝ} (hf : Integrable f P)
    (he : Integrable (fun x => exp (f x)) Q) :
    (∫ x, f x ∂P) ≤ (klDiv P Q).toReal + (∫ x, exp (f x) ∂Q) - 1 := by
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.mp hD
  have hk := (integrable_klFun_rnDeriv_iff hac).mpr hllr
  have hrf := (integrable_toReal_rnDeriv_mul_iff hac).mpr hf
  have hle := integral_mono hrf ((hk.add he).sub (integrable_const 1))
    (fun x => entropy_fenchel ENNReal.toReal_nonneg (f x))
  simp only [Pi.add_apply, Pi.sub_apply] at hle
  rw [integral_toReal_rnDeriv_mul hac, integral_sub (f := fun x => klFun (P.rnDeriv Q x).toReal + exp (f x))
      (g := fun _ => (1 : ℝ)) (hk.add he) (integrable_const 1),
    integral_add hk he, ← toReal_klDiv_eq_integral_klFun hac] at hle
  simpa using hle

theorem entropy_variational_normalized {α : Type*} [MeasurableSpace α]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hD : klDiv P Q ≠ ⊤) {f : α → ℝ} (hf : Integrable f P)
    (he : Integrable (fun x => exp (f x)) Q) (hZ : ∫ x, exp (f x) ∂Q = 1) :
    (∫ x, f x ∂P) ≤ (klDiv P Q).toReal := by
  have h := entropy_variational hD hf he
  rw [hZ] at h
  linarith

def entropyTransport (u y : ℝ) : ℝ := y - u * tanh y

def entropyTransportDeriv (u y : ℝ) : ℝ := 1 - u * (1 - tanh y ^ 2)

theorem entropyTransport_hasDerivAt (u y : ℝ) :
    HasDerivAt (entropyTransport u) (entropyTransportDeriv u y) y := by
  exact (hasDerivAt_id y).sub ((hasDerivAt_tanh y).const_mul u)

theorem entropyTransportDeriv_pos {u : ℝ} (hu : u < 1) (y : ℝ) :
    0 < entropyTransportDeriv u y := by
  have hm := tanh_sq_lt_one y
  have hm0 := sq_nonneg (tanh y)
  dsimp [entropyTransportDeriv]
  by_cases hu0 : 0 ≤ u
  · nlinarith
  · nlinarith

theorem entropyTransport_strictMono {u : ℝ} (hu : u < 1) :
    StrictMono (entropyTransport u) :=
  strictMono_of_hasDerivAt_pos (entropyTransport_hasDerivAt u) (entropyTransportDeriv_pos hu)

theorem entropyTransport_continuous (u : ℝ) : Continuous (entropyTransport u) :=
  continuous_iff_continuousAt.mpr (fun y => (entropyTransport_hasDerivAt u y).continuousAt)

theorem entropyTransport_sub_abs_le (u y : ℝ) : |entropyTransport u y - y| ≤ |u| := by
  calc
    _ = |u| * |tanh y| := by simp [entropyTransport, abs_mul]
    _ ≤ |u| * 1 := mul_le_mul_of_nonneg_left (abs_tanh_lt_one y).le (abs_nonneg _)
    _ = _ := mul_one _

theorem entropyTransport_surjective (u : ℝ) : Function.Surjective (entropyTransport u) := by
  apply (entropyTransport_continuous u).surjective
  · apply tendsto_atTop_mono' atTop (Eventually.of_forall (fun y => ?_))
      (tendsto_atTop_add_const_right atTop (-|u|) tendsto_id)
    have h := (abs_le.mp (entropyTransport_sub_abs_le u y)).1
    dsimp [id]
    linarith
  · apply tendsto_atBot_mono' atBot (Eventually.of_forall (fun y => ?_))
      (tendsto_atBot_add_const_right atBot |u| tendsto_id)
    have h := (abs_le.mp (entropyTransport_sub_abs_le u y)).2
    dsimp [id]
    linarith

theorem log_entropyTransportDeriv_lower {u : ℝ} (hu : u < 1) (y : ℝ) :
    (1 - tanh y ^ 2) * log (1 - u) ≤ log (entropyTransportDeriv u y) := by
  have hm0 := sq_nonneg (tanh y)
  have hm1 := (tanh_sq_lt_one y).le
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show 0 < (1 : ℝ) by norm_num)
    (show 0 < 1 - u by linarith) hm0 (sub_nonneg.mpr hm1)
    (show tanh y ^ 2 + (1 - tanh y ^ 2) = 1 by ring)
  simp only [smul_eq_mul, log_one, mul_zero, zero_add] at h
  convert h using 1
  congr 1
  dsimp [entropyTransportDeriv]
  ring

theorem entropyTransportDeriv_bounds {u : ℝ} (_hu : u < 1) (y : ℝ) :
    min 1 (1 - u) ≤ entropyTransportDeriv u y ∧
      entropyTransportDeriv u y ≤ max 1 (1 - u) := by
  have hm0 := sq_nonneg (tanh y)
  have hm1 := (tanh_sq_lt_one y).le
  dsimp [entropyTransportDeriv]
  by_cases hu0 : 0 ≤ u
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor <;> nlinarith
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> nlinarith

theorem integrable_log_entropyTransportDeriv {P : Measure ℝ} [IsFiniteMeasure P]
    {u : ℝ} (hu : u < 1) : Integrable (fun y => log (entropyTransportDeriv u y)) P := by
  have hm : Continuous (fun y => log (entropyTransportDeriv u y)) := by
    apply Continuous.log
    · unfold entropyTransportDeriv
      fun_prop
    · exact fun y => (entropyTransportDeriv_pos hu y).ne'
  apply Integrable.of_bound hm.aestronglyMeasurable
    (|log (min 1 (1 - u))| + |log (max 1 (1 - u))|)
  apply ae_of_all
  intro y
  have hp : 0 < min 1 (1 - u) := lt_min (by norm_num) (by linarith)
  have hlo := log_le_log hp (entropyTransportDeriv_bounds hu y).1
  have hhi := log_le_log (entropyTransportDeriv_pos hu y)
    (entropyTransportDeriv_bounds hu y).2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (log (min 1 (1 - u))),
    le_abs_self (log (max 1 (1 - u))), abs_nonneg (log (min 1 (1 - u))),
    abs_nonneg (log (max 1 (1 - u)))]

def entropyTransportLog (u d s y : ℝ) : ℝ :=
  u / s * ((y - d) * tanh y) - u ^ 2 / (2 * s) * tanh y ^ 2 +
    log (entropyTransportDeriv u y)

theorem integrable_sub_mul_tanh {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable id P) (d : ℝ) : Integrable (fun y => (y - d) * tanh y) P := by
  simpa only [Pi.sub_apply, id_eq, mul_comm] using
    (hP.sub (integrable_const d)).bdd_mul continuous_tanh.aestronglyMeasurable
      (ae_of_all _ (fun y => by simpa using (abs_tanh_lt_one y).le))

theorem integrable_entropyTransportLog {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable id P) {u : ℝ} (hu : u < 1) (d s : ℝ) :
    Integrable (entropyTransportLog u d s) P :=
  (((integrable_sub_mul_tanh hP d).const_mul (u / s)).sub
    (integrable_tanh_sq.const_mul (u ^ 2 / (2 * s)))).add
      (integrable_log_entropyTransportDeriv hu)

theorem gaussianPDF_mul_exp_transport {u d : ℝ} {s : ℝ≥0} (hu : u < 1) (y : ℝ) :
    gaussianPDFReal d s y * exp (entropyTransportLog u d s y) =
      entropyTransportDeriv u y * gaussianPDFReal d s (entropyTransport u y) := by
  unfold gaussianPDFReal entropyTransportLog
  rw [exp_add, exp_log (entropyTransportDeriv_pos hu y)]
  calc
    _ = entropyTransportDeriv u y * (1 / sqrt (2 * π * (s : ℝ))) *
      (exp (-(y - d) ^ 2 / (2 * (s : ℝ))) *
       exp (u / (s : ℝ) * ((y - d) * tanh y) - u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2)) := by ring
    _ = _ := by
      rw [← exp_add]
      rw [mul_assoc]
      have he : -(y - d) ^ 2 / (2 * (s : ℝ)) +
        (u / (s : ℝ) * ((y - d) * tanh y) - u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2) =
        -(entropyTransport u y - d) ^ 2 / (2 * (s : ℝ)) := by
          unfold entropyTransport
          ring
      rw [he]
      simp only [one_div]

theorem integrable_exp_entropyTransportLog {u d : ℝ} {s : ℝ≥0}
    (hu : u < 1) (hs : s ≠ 0) :
    Integrable (fun y => exp (entropyTransportLog u d s y)) (gaussianReal d s) := by
  rw [integrable_gaussian_iff hs]
  simp_rw [gaussianPDF_mul_exp_transport hu]
  have heq : entropyTransport u '' univ = univ := (by rw [Set.image_univ, Set.range_eq_univ.mpr (entropyTransport_surjective u)] : entropyTransport u '' univ = univ)
  have h := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun x _ => (entropyTransport_hasDerivAt u x).hasDerivWithinAt)
    ((entropyTransport_strictMono hu).monotone.monotoneOn univ) (gaussianPDFReal d s)).mp
  rw [heq, integrableOn_univ, integrableOn_univ] at h
  simpa only [smul_eq_mul] using h (integrable_gaussianPDFReal d s)

theorem integral_exp_entropyTransportLog {u d : ℝ} {s : ℝ≥0}
    (hu : u < 1) (hs : s ≠ 0) :
    (∫ y, exp (entropyTransportLog u d s y) ∂gaussianReal d s) = 1 := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  simp_rw [gaussianPDF_mul_exp_transport hu]
  have h := integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun x _ => (entropyTransport_hasDerivAt u x).hasDerivWithinAt)
    ((entropyTransport_strictMono hu).monotone.monotoneOn univ) (gaussianPDFReal d s)
  rw [(by rw [Set.image_univ, Set.range_eq_univ.mpr (entropyTransport_surjective u)] : entropyTransport u '' univ = univ)] at h
  simp only [Measure.restrict_univ, smul_eq_mul, integral_gaussianPDFReal_eq_one d hs] at h
  exact h.symm

theorem entropy_transport_lower {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable id P) {u d : ℝ} {s : ℝ≥0} (hu : u < 1) (hs : s ≠ 0)
    (hD : klDiv P (gaussianReal d s) ≠ ⊤) :
    u / (s : ℝ) * (∫ y, (y - d) * tanh y ∂P) -
      u ^ 2 / (2 * (s : ℝ)) * (∫ y, tanh y ^ 2 ∂P) +
      (1 - ∫ y, tanh y ^ 2 ∂P) * log (1 - u) ≤ (klDiv P (gaussianReal d s)).toReal := by
  have hlog := integral_mono
    (((integrable_const (1 : ℝ)).sub integrable_tanh_sq).mul_const (log (1 - u)))
    (integrable_log_entropyTransportDeriv (P := P) hu) (log_entropyTransportDeriv_lower hu)
  simp only [Pi.sub_apply] at hlog
  rw [integral_mul_const, integral_sub (integrable_const 1) integrable_tanh_sq,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at hlog
  have h := entropy_variational_normalized hD (integrable_entropyTransportLog hP hu d s)
    (integrable_exp_entropyTransportLog hu hs) (integral_exp_entropyTransportLog hu hs)
  unfold entropyTransportLog at h
  rw [integral_add (f := fun y => u / (s : ℝ) * ((y - d) * tanh y) -
      u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2)
      (((integrable_sub_mul_tanh hP d).const_mul _).sub (integrable_tanh_sq.const_mul _))
      (integrable_log_entropyTransportDeriv hu),
    integral_sub ((integrable_sub_mul_tanh hP d).const_mul _) (integrable_tanh_sq.const_mul _),
    integral_const_mul, integral_const_mul] at h
  linarith

theorem log_gaussianPDFReal {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    log (gaussianPDFReal d s y) = -log (2 * π * (s : ℝ)) / 2 -
      (y - d) ^ 2 / (2 * (s : ℝ)) := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hp : 0 < 2 * π * (s : ℝ) := by positivity
  unfold gaussianPDFReal
  rw [log_mul (by positivity) (exp_pos _).ne', log_inv, log_sqrt hp.le, log_exp]
  ring

def gaussianRatioLog (d : ℝ) (s r : ℝ≥0) (y : ℝ) : ℝ :=
  log (gaussianPDFReal d r y) - log (gaussianPDFReal d s y)

theorem gaussianRatioLog_formula {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) (y : ℝ) :
    gaussianRatioLog d s r y = (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (y - d) ^ 2 := by
  have hsp : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  have hrp : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hr
  rw [gaussianRatioLog, log_gaussianPDFReal hr, log_gaussianPDFReal hs,
    log_mul (by positivity : (2 : ℝ) * π ≠ 0) hrp,
    log_mul (by positivity : (2 : ℝ) * π ≠ 0) hsp]
  ring

theorem gaussianPDF_mul_exp_ratio {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) (y : ℝ) :
    gaussianPDFReal d s y * exp (gaussianRatioLog d s r y) = gaussianPDFReal d r y := by
  rw [gaussianRatioLog, exp_sub, exp_log (gaussianPDFReal_pos d r y hr),
    exp_log (gaussianPDFReal_pos d s y hs)]
  exact mul_div_cancel₀ _ (gaussianPDFReal_pos d s y hs).ne'

theorem integrable_gaussianRatioLog {P : Measure ℝ} [IsFiniteMeasure P]
    {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P) : Integrable (gaussianRatioLog d s r) P := by
  change Integrable (fun y => gaussianRatioLog d s r y) P
  simp_rw [gaussianRatioLog_formula hs hr]
  exact (integrable_const ((log (s : ℝ) - log (r : ℝ)) / 2)).add (hP.const_mul _)

theorem integrable_exp_gaussianRatioLog {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) :
    Integrable (fun y => exp (gaussianRatioLog d s r y)) (gaussianReal d s) := by
  rw [integrable_gaussian_iff hs]
  simp_rw [gaussianPDF_mul_exp_ratio hs hr]
  exact integrable_gaussianPDFReal d r

theorem integral_exp_gaussianRatioLog {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) :
    (∫ y, exp (gaussianRatioLog d s r y) ∂gaussianReal d s) = 1 := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  simp_rw [gaussianPDF_mul_exp_ratio hs hr]
  exact integral_gaussianPDFReal_eq_one d hr

theorem entropy_variance_comparison {P : Measure ℝ} [IsProbabilityMeasure P]
    {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P)
    (hD : klDiv P (gaussianReal d s) ≠ ⊤) :
    (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (∫ y, (y - d) ^ 2 ∂P) ≤
      (klDiv P (gaussianReal d s)).toReal := by
  have h := entropy_variational_normalized hD (integrable_gaussianRatioLog hs hr hP)
    (integrable_exp_gaussianRatioLog hs hr) (integral_exp_gaussianRatioLog hs hr)
  simp_rw [gaussianRatioLog_formula hs hr] at h
  rw [integral_add (integrable_const _) (hP.const_mul _), integral_const_mul] at h
  simpa using h

theorem entropy_variance_lower {P : Measure ℝ} [IsProbabilityMeasure P]
    {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P)
    (hD : klDiv P (gaussianReal d s) ≠ ⊤) {v : ℝ} (hv : 0 < v)
    (hvar : ∫ y, (y - d) ^ 2 ∂P = (s : ℝ) * v) :
    (v - 1 - log v) / 2 ≤ (klDiv P (gaussianReal d s)).toReal := by
  let r : ℝ≥0 := s * ⟨v, hv.le⟩
  have hr : r ≠ 0 := mul_ne_zero hs (NNReal.coe_ne_zero.mp hv.ne')
  have h := entropy_variance_comparison hs hr hP hD
  change (log (s : ℝ) - log ((s : ℝ) * v)) / 2 +
    (1 / (2 * (s : ℝ)) - 1 / (2 * ((s : ℝ) * v))) *
      (∫ y, (y - d) ^ 2 ∂P) ≤ _ at h
  have hsp : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  rw [log_mul hsp hv.ne', hvar] at h
  convert h using 1
  field_simp
  ring

theorem secondMoment_integrable {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P) : Integrable id P := by
  exact ((memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable id P)).mpr hP).integrable (by norm_num)

theorem centered_secondMoment_integrable {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P) (d : ℝ) :
    Integrable (fun y => (y - d) ^ 2) P := by
  have hm : MemLp id 2 P := (memLp_two_iff_integrable_sq (by fun_prop)).mpr hP
  exact (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y - d) P)).mp
    (hm.sub (memLp_const d))

theorem entropy_q_pos {P : Measure ℝ} [IsProbabilityMeasure P]
    {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) (hD : klDiv P (gaussianReal d s) ≠ ⊤) :
    0 < ∫ y, tanh y ^ 2 ∂P := by
  have := nullSingletonClass_gaussianReal (μ := d) hs
  have hzero : P {0} = 0 := (klDiv_ne_top_iff.mp hD).1 (measure_singleton 0)
  have hsupp : Function.support (fun y : ℝ => tanh y ^ 2) = ({0} : Set ℝ)ᶜ := by
    ext y
    simp only [Function.mem_support, mem_compl_iff, mem_singleton_iff, ne_eq, sq_eq_zero_iff]
    have he : tanh y = 0 ↔ y = 0 := by
      simpa only [tanh_zero] using (show tanh y = tanh 0 ↔ y = 0 from tanh_injective.eq_iff)
    exact not_congr he
  rw [integral_pos_iff_support_of_nonneg (fun y => sq_nonneg (tanh y)) integrable_tanh_sq, hsupp,
    measure_compl (measurableSet_singleton 0) (by simp), hzero]
  simp

theorem entropy_q_lt_one {P : Measure ℝ} [IsProbabilityMeasure P] :
    (∫ y, tanh y ^ 2 ∂P) < 1 := by
  have hi : Integrable (fun y : ℝ => 1 - tanh y ^ 2) P := (integrable_const 1).sub integrable_tanh_sq
  have hsupp : Function.support (fun y : ℝ => 1 - tanh y ^ 2) = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (sub_pos.mpr (tanh_sq_lt_one y)).ne'
  have hp := (integral_pos_iff_support_of_nonneg (fun y => (sub_pos.mpr (tanh_sq_lt_one y)).le) hi).mpr
    (by rw [hsupp]; simp)
  rw [integral_sub (integrable_const 1) integrable_tanh_sq] at hp
  simpa using hp

theorem entropy_moment_cauchy {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P) (d : ℝ)
    (hq : 0 < ∫ y, tanh y ^ 2 ∂P) :
    (∫ y, (y - d) * tanh y ∂P) ^ 2 ≤
      (∫ y, tanh y ^ 2 ∂P) * (∫ y, (y - d) ^ 2 ∂P) := by
  let a := ∫ y, (y - d) * tanh y ∂P
  let q := ∫ y, tanh y ^ 2 ∂P
  have hp : 0 ≤ ∫ y : ℝ, ((y - d) - (a / q) * tanh y) ^ 2 ∂P :=
    integral_nonneg (fun y => sq_nonneg _)
  have he (y : ℝ) : ((y - d) - (a / q) * tanh y) ^ 2 =
      (y - d) ^ 2 - (2 * a / q) * ((y - d) * tanh y) + (a / q) ^ 2 * tanh y ^ 2 := by ring
  simp_rw [he] at hp
  have hv := centered_secondMoment_integrable hP d
  have ha := integrable_sub_mul_tanh (secondMoment_integrable hP) d
  rw [integral_add (f := fun y => (y - d) ^ 2 - (2 * a / q) * ((y - d) * tanh y))
      (hv.sub (ha.const_mul (2 * a / q))) (integrable_tanh_sq.const_mul ((a / q) ^ 2)),
    integral_sub hv (ha.const_mul (2 * a / q)), integral_const_mul, integral_const_mul] at hp
  change 0 ≤ (∫ y, (y - d) ^ 2 ∂P) - 2 * a / q * a + (a / q) ^ 2 * q at hp
  have hqp : 0 < q := hq
  have hm := mul_nonneg hp hqp.le
  field_simp at hm
  dsimp [a, q] at hm
  nlinarith

end SKGap

noncomputable section
open Real Set

end
end
end

end OAI

import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussianSmallBall
import OAI.Computability.MinUncut.Estimates.NormalizedWeights

namespace OAI

noncomputable section
open MeasureTheory
namespace MinUncut.FiniteGaussian

def baseDensity (v : ℝ) : ℝ := Real.exp (-v^2/2)
def gIntegral (a b : ℝ) : ℝ := ∫ v in a..b, baseDensity v

lemma continuous_baseDensity : Continuous baseDensity := by unfold baseDensity; fun_prop

lemma gIntegral_pos {a b : ℝ} (hab : a < b) : 0 < gIntegral a b := by
  apply intervalIntegral.integral_pos hab continuous_baseDensity.continuousOn
  · intro v _; exact (Real.exp_pos _).le
  · exact ⟨a,⟨le_rfl,hab.le⟩,Real.exp_pos _⟩

lemma gIntegral_large {T : ℝ} (hT : 1 ≤ T) : 1 < gIntegral (-T) T := by
  have hbase : (5/3:ℝ) ≤ gIntegral (-1) 1 := by
    have hh := intervalIntegral.integral_mono (a := (-1:ℝ)) (b := 1) (by norm_num)
      (show IntervalIntegrable (fun v : ℝ => 1-v^2/2) volume (-1) 1 from
        (by fun_prop : Continuous (fun v : ℝ => 1-v^2/2)).intervalIntegrable _ _)
      (continuous_baseDensity.intervalIntegrable _ _)
      (fun v => (show 1-v^2/2 ≤ baseDensity v by
        have := Real.add_one_le_exp (-v^2/2)
        dsimp [baseDensity]; linarith))
    have he : (∫ v in (-1:ℝ)..1, 1-v^2/2)=(5/3:ℝ) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const)
        ((show Continuous (fun v : ℝ => v^2/2) by fun_prop).intervalIntegrable _ _)]
      rw [intervalIntegral.integral_div,integral_pow]
      norm_num
    simpa only [he,gIntegral] using hh
  have hle : gIntegral (-1) 1 ≤ gIntegral (-T) T := by
    exact intervalIntegral.integral_mono_interval (by linarith) (by norm_num) hT
      (Filter.Eventually.of_forall (fun v => (Real.exp_pos _).le))
      (continuous_baseDensity.intervalIntegrable _ _)
  linarith

lemma residual_bounds {T : ℚ} (hT : 0 ≤ T) (r : ℕ) :
    0 ≤ (qIntegral r (-T) T:ℝ)-gIntegral (-T) T ∧
      (qIntegral r (-T) T:ℝ)-gIntegral (-T) T ≤ 2*(T:ℝ)*error r ((T:ℝ)^2/2) := by
  have hT' : (0:ℝ) ≤ T := by exact_mod_cast hT
  have hh : (qIntegral r (-T) T:ℝ)-gIntegral (-T) T =
      ∫ v in -(T:ℝ)..(T:ℝ), densityPolynomial r v-baseDensity v := by
    rw [qIntegral_cast]
    push_cast
    rw [intervalIntegral.integral_sub (continuous_density r |>.intervalIntegrable _ _)
      (continuous_baseDensity.intervalIntegrable _ _)]
    rfl
  rw [hh]
  have hf : IntervalIntegrable (fun v => densityPolynomial r v-baseDensity v) volume (-T) T :=
    ((continuous_density r).sub continuous_baseDensity).intervalIntegrable _ _
  constructor
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro v hv
    exact (density_bounds hT' (abs_le.mpr hv) r).1
  · have hb := intervalIntegral.integral_mono_on (a := -(T:ℝ)) (b := (T:ℝ))
      (by linarith) hf intervalIntegrable_const
      (fun v hv => (density_bounds hT' (abs_le.mpr hv) r).2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,sub_neg_eq_add,two_mul] using hb

open scoped BigOperators
open MeasureTheory

def gCell (T : ℚ) (L : ℕ) (i : Fin L) : ℝ :=
  gIntegral (endpoint T L i) (endpoint T L (i+1))

def qCell (r : ℕ) (T : ℚ) (L : ℕ) (i : Fin L) : ℝ :=
  qIntegral r (endpoint T L i) (endpoint T L (i+1))

lemma sum_gCell (T : ℚ) {L : ℕ} (hL : 0 < L) :
    (∑ i : Fin L, gCell T L i)=gIntegral (-T) T := by
  unfold gCell gIntegral
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ∫ v in (endpoint T L i:ℝ)..(endpoint T L (i+1):ℝ), baseDensity v)]
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ => continuous_baseDensity.intervalIntegrable _ _)]
  rw [endpoint_zero,endpoint_end T hL]
  norm_cast

lemma sum_qCell (r : ℕ) (T : ℚ) {L : ℕ} (hL : 0 < L) :
    (∑ i : Fin L, qCell r T L i)=(qIntegral r (-T) T:ℝ) := by
  unfold qCell qIntegral
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((primitive r (endpoint T L (i+1))-primitive r (endpoint T L i):ℚ):ℝ))]
  push_cast
  rw [Finset.sum_range_sub (fun i => (primitive r (endpoint T L i):ℝ)),endpoint_zero,endpoint_end T hL]

lemma gCell_nonneg {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L) (i : Fin L) :
    0 ≤ gCell T L i := by
  exact (gIntegral_pos (by exact_mod_cast endpoint_lt hT hL i)).le

lemma gCell_le_qCell {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L) (r : ℕ) (i : Fin L) :
    gCell T L i ≤ qCell r T L i := by
  unfold gCell qCell gIntegral
  rw [qIntegral_cast]
  apply intervalIntegral.integral_mono (by exact_mod_cast (endpoint_lt hT hL i).le)
    (continuous_baseDensity.intervalIntegrable _ _) ((continuous_density r).intervalIntegrable _ _)
  intro v
  have hh := (evenExp_error (by positivity : 0 ≤ v^2/2) r).1
  dsimp [densityPolynomial,baseDensity]
  simpa only [neg_div] using (sub_nonneg.mp hh)

lemma grid_product_bound {T : ℚ} (hT : 1 ≤ T) {L : ℕ} (hL : 0 < L)
    (r d : ℕ) (F : (Fin d → Fin L) → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    |(∑ x, (∏ i, qCell r T L (x i))*F x)/(qIntegral r (-T) T:ℝ)^d-
      (∑ x, (∏ i, gCell T L (x i))*F x)/(gIntegral (-T) T)^d| ≤
        2*d*(T:ℝ)*error r ((T:ℝ)^2/2) := by
  have hT0 : 0 < T := by linarith
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hb := finite_product_test_bound (qCell r T L) (gCell T L)
    (gCell_nonneg hT0 hL) (gCell_le_qCell hT0 hL r)
    (by rw [sum_gCell T hL]; exact (gIntegral_large hT').le) d F hF
  rw [sum_qCell r T hL,sum_gCell T hL] at hb
  exact hb.trans (by
    have hh := mul_le_mul_of_nonneg_left (residual_bounds hT0.le r).2 (Nat.cast_nonneg (α := ℝ) d)
    nlinarith)

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

abbrev gaussianConstant : ℝ := (Real.sqrt (2*Real.pi))⁻¹

lemma gaussianConstant_pos : 0 < gaussianConstant := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

lemma gaussian_Ioc {a b : ℚ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Ioc (a:ℝ) b)=gaussianConstant*gIntegral a b := by
  rw [Measure.real,gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  have he : gaussianPDFReal 0 1=fun x => gaussianConstant*baseDensity x := by
    ext x
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,baseDensity]
  rw [he,integral_const_mul]
  congr 1
  exact (intervalIntegral.integral_of_le (by exact_mod_cast hab)).symm

lemma gaussian_cube_pos {ι : Type*} [Fintype ι] {T : ℚ} (hT : 0 < T) :
    0 < (Measure.pi (fun _ : ι => gaussianReal 0 1)).real (cube T) := by
  unfold cube Measure.real
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  apply Finset.prod_pos
  intro i _
  change 0 < (gaussianReal 0 1).real (Ioc (-(T:ℝ)) T)
  rw [show -(T:ℝ)=((-T:ℚ):ℝ) by norm_cast,gaussian_Ioc (by linarith)]
  exact mul_pos gaussianConstant_pos (gIntegral_pos (by exact_mod_cast (show -T<T by linarith)))

lemma gaussian_cube {ι : Type*} [Fintype ι] {T : ℚ} (hT : 0 ≤ T) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).real (cube T)=
      gaussianConstant^(Fintype.card ι)*(gIntegral (-T) T)^(Fintype.card ι) := by
  unfold cube Measure.real
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ _ : ι, (gaussianReal 0 1).real (Ioc (-(T:ℝ)) T))=_
  simp only [show -(T:ℝ)=((-T:ℚ):ℝ) by norm_cast,gaussian_Ioc (by linarith : -T≤T),
    Finset.prod_const,Finset.card_univ,mul_pow]

lemma gaussian_cubeCell {ι : Type*} [Fintype ι] {T : ℚ} (hT : 0 < T)
    {L : ℕ} (hL : 0 < L) (j : ι → Fin L) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).real (cubeCell T L j)=
      gaussianConstant^(Fintype.card ι)*∏ i, gCell T L (j i) := by
  unfold cubeCell cell Measure.real
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ i, (gaussianReal 0 1).real (Ioc (endpoint T L (j i):ℝ) (endpoint T L (j i+1))))=_
  simp only [gaussian_Ioc (endpoint_lt hT hL _).le]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,gCell]

end MinUncut.FiniteGaussian

end

end OAI

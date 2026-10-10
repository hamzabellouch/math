import OAI.Geometry.LatticeCovering.Model

namespace OAI


section





section



noncomputable section
open scoped BigOperators
open Real

namespace SingleLatticeCovering.Folded
variable {ι : Type*} [Fintype ι]

def gamma1 (x : ℝ) : ℝ := Real.exp (-(x^2)/2) / Real.sqrt (2*Real.pi)
def gamma (x : ι → ℝ) : ℝ := ∏ j, gamma1 (x j)
def height (b : ℕ) : ℝ := Real.sqrt ((9/4 : ℝ)*Real.log (b : ℝ))
def density (h t : ℝ) : ℝ := h*gamma1 (h*t)+h*gamma1 (h*(t-1))
def folded (h : ℝ) (t : ι → ℝ) : ℝ := ∏ j, density h (t j)
def bitValue (e : Bool) : ℝ := if e then 1 else 0
def probability (h t : ℝ) (e : Bool) : ℝ :=
  h*gamma1 (h*(t-bitValue e))/density h t
def wordMass (h : ℝ) (t : ι → ℝ) (e : ι → Bool) : ℝ := ∏ j, probability h (t j) (e j)
def atom (h : ℝ) (t : ι → ℝ) (e : ι → Bool) : ℝ :=
  h^Fintype.card ι * gamma (fun j => h*(t j-bitValue (e j)))

def alpha : ℝ := (1+Real.exp 1)⁻¹

lemma gamma1_pos (x : ℝ) : 0 < gamma1 x :=
  div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos))

lemma density_pos {h : ℝ} (hh : 0 < h) (t : ℝ) : 0 < density h t :=
  add_pos (mul_pos hh (gamma1_pos _)) (mul_pos hh (gamma1_pos _))

lemma folded_pos {h : ℝ} (hh : 0 < h) (t : ι → ℝ) : 0 < folded h t :=
  Finset.prod_pos (fun _ _ => density_pos hh _)

lemma alpha_pos : 0 < alpha := by unfold alpha; positivity
lemma alpha_lt_one : alpha < 1 := by
  apply (inv_lt_one₀ (by positivity : (0 : ℝ) < 1+exp 1)).mpr
  linarith [Real.exp_pos (1 : ℝ)]

lemma probability_sum {h : ℝ} (hh : 0 < h) (t : ℝ) :
    probability h t false + probability h t true = 1 := by
  simp only [probability, bitValue, Bool.false_eq_true, ↓reduceIte, sub_zero,
    ← add_div]
  exact div_self (density_pos hh t).ne'

lemma probability_pos {h : ℝ} (hh : 0 < h) (t : ℝ) (e : Bool) :
    0 < probability h t e :=
  div_pos (mul_pos hh (gamma1_pos _)) (density_pos hh _)

lemma probability_le_one {h : ℝ} (hh : 0 < h) (t : ℝ) (e : Bool) :
    probability h t e ≤ 1 := by
  have hs := probability_sum hh t
  have hf := (probability_pos hh t false).le
  have ht := (probability_pos hh t true).le
  cases e <;> linarith

lemma wordMass_sum [DecidableEq ι] {h : ℝ} (hh : 0 < h) (t : ι → ℝ) :
    (∑ e : ι → Bool, wordMass h t e) = 1 := by
  unfold wordMass
  rw [← Fintype.prod_sum]
  have hs (j : ι) : (∑ e : Bool, probability h (t j) e) = 1 := by
    rw [Fintype.sum_bool]
    linarith [probability_sum hh (t j)]
  simp only [hs, Finset.prod_const_one]

lemma folded_identity {h : ℝ} (hh : 0 < h) (t : ι → ℝ) (e : ι → Bool) :
    atom h t e = folded h t * wordMass h t e := by
  have ha : atom h t e = ∏ j, h*gamma1 (h*(t j-bitValue (e j))) := by
    simp [atom, gamma, Finset.prod_mul_distrib]
  rw [ha, folded, wordMass, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [probability]
  field_simp [(density_pos hh (t j)).ne']

lemma gaussian_ratio (h t : ℝ) :
    gamma1 (h*t) = Real.exp (h^2*(1/2-t))*gamma1 (h*(t-1)) := by
  have he : -(h*t)^2/2 = h^2*(1/2-t) + -(h*(t-1))^2/2 := by ring
  simp only [gamma1, he, Real.exp_add]
  ring

lemma probability_true_logistic {h : ℝ} (hh : 0 < h) (t : ℝ) :
    probability h t true = (1+Real.exp (h^2*(1/2-t)))⁻¹ := by
  have hg := (gamma1_pos (h*(t-1))).ne'
  unfold probability density
  simp only [bitValue, ↓reduceIte]
  rw [gaussian_ratio h t]
  field_simp
  ring

lemma one_sub_logistic (s : ℝ) :
    1-(1+Real.exp s)⁻¹ = (1+Real.exp (-s))⁻¹ := by
  rw [Real.exp_neg]
  field_simp
  ring

lemma logistic_lower {s : ℝ} (hs : s ≤ 1) : alpha ≤ (1+Real.exp s)⁻¹ := by
  simpa only [alpha, one_div] using
    one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1+exp s)
      (add_le_add_right (Real.exp_le_exp.mpr hs) 1)

lemma probability_central {h t : ℝ} (hh : 0 < h)
    (ht : |t-1/2| ≤ (h^2)⁻¹) (e : Bool) :
    alpha ≤ probability h t e ∧ probability h t e ≤ 1-alpha := by
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  have hprod := mul_le_mul_of_nonneg_left ht hh2.le
  rw [mul_inv_cancel₀ hh2.ne'] at hprod
  have hab := abs_le.mp ht
  have h1 : h^2*(1/2-t) ≤ 1 := by
    calc _ ≤ h^2*|t-1/2| := mul_le_mul_of_nonneg_left (by linarith [neg_le_abs (t-1/2)] : 1/2-t ≤ |t-1/2|) hh2.le
         _ ≤ 1 := hprod
  have h2 : -(h^2*(1/2-t)) ≤ 1 := by
    calc _ ≤ h^2*|t-1/2| := by nlinarith [le_abs_self (t-1/2)]
         _ ≤ 1 := hprod
  have hp := logistic_lower h1
  have hn := logistic_lower h2
  rw [← probability_true_logistic hh t] at hp
  rw [← one_sub_logistic, ← probability_true_logistic hh t] at hn
  have hs := probability_sum hh t
  cases e <;> constructor <;> linarith

lemma wordMass_le_exp_card {h : ℝ} (hh : 0 < h) (t : ι → ℝ) (e : ι → Bool)
    (S : Finset ι) (hS : ∀ j ∈ S, |t j-1/2| ≤ (h^2)⁻¹) :
    wordMass h t e ≤ Real.exp (-alpha*(S.card : ℝ)) := by
  classical
  have he : 1-alpha ≤ Real.exp (-alpha) := by
    have h := Real.add_one_le_exp (-alpha)
    linarith
  calc
    _ ≤ ∏ j : ι, Real.exp (if j ∈ S then -alpha else 0) := by
      apply Finset.prod_le_prod₀ (fun j _ => (probability_pos hh _ _).le)
      intro j _
      by_cases hj : j ∈ S
      · simp only [hj, ↓reduceIte]
        exact (probability_central hh (hS j hj) _).2.trans he
      · simp only [hj, ↓reduceIte, Real.exp_zero]
        exact probability_le_one hh _ _
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp [Finset.sum_ite_mem, mul_comm]



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set


def totalMass (h : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, density h t

def logMean (h : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, density h t*Real.log (density h t))/totalMass h

lemma continuous_gamma1 : Continuous gamma1 := by
  unfold gamma1
  fun_prop

lemma continuous_density (h : ℝ) : Continuous (density h) := by
  unfold density
  exact (continuous_const.mul (continuous_gamma1.comp (continuous_const.mul continuous_id))).add
    (continuous_const.mul (continuous_gamma1.comp (continuous_const.mul (continuous_id.sub continuous_const))))

lemma gamma1_eq_gaussianPDF (x : ℝ) : gamma1 x = gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, gamma1]
  ring

lemma gamma1_even (x : ℝ) : gamma1 (-x) = gamma1 x := by simp [gamma1]

lemma gamma1_int : ∫ x : ℝ, gamma1 x = 1 := by
  simp_rw [gamma1_eq_gaussianPDF]
  exact integral_gaussianPDFReal_eq_one 0 (by norm_num)

lemma gamma1_integrable : Integrable gamma1 := by
  have he : gamma1 = gaussianPDFReal 0 1 := funext gamma1_eq_gaussianPDF
  rw [he]
  exact integrable_gaussianPDFReal _ _

lemma totalMass_eq_integral {h : ℝ} (hh : 0 < h) :
    totalMass h = ∫ x in -h..h, gamma1 x := by
  unfold totalMass density
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_mul_left gamma1 hh.ne']
    have hs : (∫ t in (0 : ℝ)..1, gamma1 (h*(t-1))) =
        h⁻¹ * ∫ x in -h..0, gamma1 x := by
      calc
        _ = ∫ t in (0 : ℝ)..1, (fun u => gamma1 (h*u)) (t-1) := rfl
        _ = ∫ t in (-1 : ℝ)..0, gamma1 (h*t) := by
          simpa using (intervalIntegral.integral_comp_sub_right
            (fun u => gamma1 (h*u)) (a := 0) (b := 1) 1)
        _ = _ := by rw [intervalIntegral.integral_comp_mul_left gamma1 hh.ne']; simp
    rw [hs]
    simp only [mul_zero, mul_one, smul_eq_mul]
    rw [←mul_assoc, mul_inv_cancel₀ hh.ne', one_mul, ←mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (continuous_gamma1.intervalIntegrable _ _) (continuous_gamma1.intervalIntegrable _ _)
  · exact (continuous_const.mul (continuous_gamma1.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_gamma1.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable _ _

lemma totalMass_pos {h : ℝ} (hh : 0 < h) : 0 < totalMass h := by
  unfold totalMass
  apply intervalIntegral.integral_pos
  · norm_num
  · exact (continuous_density h).continuousOn
  · intro x hx
    exact (density_pos hh x).le
  · exact ⟨0, by norm_num, density_pos hh 0⟩

lemma totalMass_le_one {h : ℝ} (hh : 0 < h) : totalMass h ≤ 1 := by
  rw [totalMass_eq_integral hh, intervalIntegral.integral_of_le (by linarith : -h ≤ h)]
  rw [←gamma1_int]
  exact setIntegral_le_integral gamma1_integrable (Filter.Eventually.of_forall (fun x => (gamma1_pos x).le))

lemma gamma1_le_inv_sqrt (x : ℝ) : gamma1 x ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
  unfold gamma1
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos))).mpr
  rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne']
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])

lemma density_upper {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    density h t ≤ 2*h/Real.sqrt (2*Real.pi) := by
  have h0 := mul_le_mul_of_nonneg_left (gamma1_le_inv_sqrt (h*t)) hh
  have h1 := mul_le_mul_of_nonneg_left (gamma1_le_inv_sqrt (h*(t-1))) hh
  unfold density
  rw [div_eq_mul_inv]
  nlinarith

lemma density_lower {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc 0 1) :
    h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8) ≤ density h t := by
  have hbase {x : ℝ} (hx : |x| ≤ 1/2) :
      h/Real.sqrt (2*Real.pi)*Real.exp (-(h^2)/8) ≤ h*gamma1 (h*x) := by
    have hx' := abs_le.mp hx
    have hs : (h*x)^2 ≤ h^2/4 := by
      have hsq : x^2 ≤ 1/4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg h)]
    have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show -(h^2)/8 ≤ -(h*x)^2/2 by nlinarith))
      (show 0 ≤ h/Real.sqrt (2*Real.pi) by positivity)
    simpa only [gamma1, div_mul_eq_mul_div, mul_div_assoc] using he
  by_cases ht2 : t ≤ 1/2
  · have hz := hbase (abs_le.mpr ⟨by linarith [ht.1],ht2⟩)
    exact hz.trans (le_add_of_nonneg_right (mul_nonneg hh.le (gamma1_pos _).le))
  · have hz := hbase (x := t-1) (abs_le.mpr ⟨by linarith,by linarith [ht.2]⟩)
    exact hz.trans (le_add_of_nonneg_left (mul_nonneg hh.le (gamma1_pos _).le))



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real

lemma gaussian_subgaussian : HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) where
  integrable_exp_mul := integrable_exp_mul_gaussianReal
  mgf_le t := by simp [mgf_fun_id_gaussianReal]

lemma totalMass_eq_probability {h : ℝ} (hh : 0 < h) :
    totalMass h = (gaussianReal 0 1).real (Ioc (-h) h) := by
  rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  rw [totalMass_eq_integral hh, intervalIntegral.integral_of_le (by linarith : -h ≤ h)]
  exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => gamma1_eq_gaussianPDF x)


lemma totalMass_tail {h : ℝ} (hh : 0 < h) :
    1-totalMass h ≤ 2*Real.exp (-h^2/2) := by
  rw [totalMass_eq_probability hh]
  have hc : (gaussianReal 0 1).real ((Ioc (-h) h)ᶜ) =
      1-(gaussianReal 0 1).real (Ioc (-h) h) := by
    rw [measureReal_compl measurableSet_Ioc]
    simp
  rw [←hc]
  have hs : (Ioc (-h) h)ᶜ ⊆ {x : ℝ | h ≤ -x} ∪ {x : ℝ | h ≤ x} := by
    intro x hx
    simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inl (by dsimp; linarith)
    · exact Or.inr hx.le
  calc
    _ ≤ (gaussianReal 0 1).real ({x : ℝ | h ≤ -x} ∪ {x : ℝ | h ≤ x}) :=
      measureReal_mono hs
    _ ≤ (gaussianReal 0 1).real {x : ℝ | h ≤ -x} +
        (gaussianReal 0 1).real {x : ℝ | h ≤ x} := measureReal_union_le _ _
    _ ≤ _ := by
      have hl := gaussian_subgaussian.neg.measure_ge_le hh.le
      have hr := gaussian_subgaussian.measure_ge_le hh.le
      simp only [Pi.neg_apply, NNReal.coe_one, mul_one] at hl hr
      linarith

lemma gamma1_second_int : ∫ x : ℝ, gamma1 x * x^2 = 1 := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hv
  simp only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] at hv
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)] at hv
  simpa only [←gamma1_eq_gaussianPDF, smul_eq_mul] using hv

lemma gamma1_second_integrable : Integrable (fun x : ℝ => gamma1 x*x^2) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)
    (s := 2) (by norm_num)).div_const (Real.sqrt (2*Real.pi))
  convert hi using 1
  ext x
  rw [Real.rpow_two]
  unfold gamma1
  rw [show -(x^2)/2 = -(1/2 : ℝ)*x^2 by ring]
  ring



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real

lemma integral_fold {φ : ℝ → ℝ} (hφ : Continuous φ) {h : ℝ} (hh : 0 < h) :
    (∫ t in (0 : ℝ)..1, h*φ (h*t)+h*φ (h*(t-1))) = ∫ x in -h..h, φ x := by
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_mul_left φ hh.ne']
    have hs : (∫ t in (0 : ℝ)..1, φ (h*(t-1))) = h⁻¹ * ∫ x in -h..0, φ x := by
      calc
        _ = ∫ t in (0 : ℝ)..1, (fun u => φ (h*u)) (t-1) := rfl
        _ = ∫ t in (-1 : ℝ)..0, φ (h*t) := by
          simpa using (intervalIntegral.integral_comp_sub_right
            (fun u => φ (h*u)) (a := 0) (b := 1) 1)
        _ = _ := by rw [intervalIntegral.integral_comp_mul_left φ hh.ne']; simp
    rw [hs]
    simp only [mul_zero, mul_one, smul_eq_mul]
    rw [←mul_assoc, mul_inv_cancel₀ hh.ne', one_mul, ←mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hφ.intervalIntegrable _ _) (hφ.intervalIntegrable _ _)
  · exact (continuous_const.mul (hφ.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · exact (continuous_const.mul (hφ.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable _ _

def foldMoment (h t : ℝ) : ℝ :=
  h*(gamma1 (h*t)*(h*t)^2)+h*(gamma1 (h*(t-1))*(h*(t-1))^2)

lemma continuous_foldMoment (h : ℝ) : Continuous (foldMoment h) := by
  unfold foldMoment
  exact (continuous_const.mul ((continuous_gamma1.comp (continuous_const.mul continuous_id)).mul
    ((continuous_const.mul continuous_id).pow 2))).add
    (continuous_const.mul ((continuous_gamma1.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).mul
      ((continuous_const.mul (continuous_id.sub continuous_const)).pow 2)))

lemma foldMoment_integral_le {h : ℝ} (hh : 0 < h) :
    (∫ t in (0 : ℝ)..1, foldMoment h t) ≤ 1 := by
  unfold foldMoment
  rw [integral_fold (φ := fun x => gamma1 x*x^2)
    (continuous_gamma1.mul (continuous_id.pow 2)) hh,
    intervalIntegral.integral_of_le (by linarith : -h ≤ h), ←gamma1_second_int]
  exact setIntegral_le_integral gamma1_second_integrable
    (Filter.Eventually.of_forall (fun x => mul_nonneg (gamma1_pos x).le (sq_nonneg x)))

lemma log_component {h : ℝ} (hh : 0 < h) (x : ℝ) :
    Real.log (h*gamma1 (h*x)) = Real.log h-Real.log (Real.sqrt (2*Real.pi))-(h*x)^2/2 := by
  rw [Real.log_mul hh.ne' (gamma1_pos _).ne', gamma1,
    Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne',
    Real.log_exp]
  ring

lemma entropy_lower_pointwise {h : ℝ} (hh : 0 < h) (t : ℝ) :
    (Real.log h-Real.log (Real.sqrt (2*Real.pi)))*density h t-foldMoment h t/2 ≤
      density h t*Real.log (density h t) := by
  have hp0 : 0 < h*gamma1 (h*t) := mul_pos hh (gamma1_pos _)
  have hp1 : 0 < h*gamma1 (h*(t-1)) := mul_pos hh (gamma1_pos _)
  have hl0 := Real.log_le_log hp0 (show h*gamma1 (h*t) ≤ density h t by
    unfold density; linarith)
  have hl1 := Real.log_le_log hp1 (show h*gamma1 (h*(t-1)) ≤ density h t by
    unfold density; linarith)
  rw [log_component hh] at hl0 hl1
  have h0 := mul_le_mul_of_nonneg_left hl0 hp0.le
  have h1 := mul_le_mul_of_nonneg_left hl1 hp1.le
  unfold density foldMoment at *
  nlinarith

lemma logMean_upper {h : ℝ} (hh : 0 < h) :
    logMean h ≤ Real.log (2*h/Real.sqrt (2*Real.pi)) := by
  have hc : Continuous (fun t => density h t*Real.log (density h t)) :=
    (continuous_density h).mul ((continuous_density h).log (fun t => (density_pos hh t).ne'))
  have hl : (∫ t in (0 : ℝ)..1, density h t*Real.log (density h t)) ≤
      (∫ t in (0 : ℝ)..1, density h t*Real.log (2*h/Real.sqrt (2*Real.pi))) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _)
      (((continuous_density h).mul continuous_const).intervalIntegrable _ _)
    intro t ht
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (density_pos hh t)
      (density_upper hh.le t)) (density_pos hh t).le
  rw [intervalIntegral.integral_mul_const] at hl
  exact (div_le_iff₀ (totalMass_pos hh)).mpr (by simpa [mul_comm, totalMass] using hl)

lemma logMean_lower {h : ℝ} (hh : 0 < h) :
    Real.log h-Real.log (Real.sqrt (2*Real.pi))-1/(2*totalMass h) ≤ logMean h := by
  have hc : Continuous (fun t => density h t*Real.log (density h t)) :=
    (continuous_density h).mul ((continuous_density h).log (fun t => (density_pos hh t).ne'))
  have hl : (∫ t in (0 : ℝ)..1,
      (Real.log h-Real.log (Real.sqrt (2*Real.pi)))*density h t-foldMoment h t/2) ≤
      (∫ t in (0 : ℝ)..1, density h t*Real.log (density h t)) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ (hc.intervalIntegrable _ _) ?_
    · exact ((continuous_const.mul (continuous_density h)).sub
        ((continuous_foldMoment h).div_const 2)).intervalIntegrable _ _
    · intro t ht
      exact entropy_lower_pointwise hh t
  have hi₁ : IntervalIntegrable (fun t =>
      (Real.log h-Real.log (Real.sqrt (2*Real.pi)))*density h t) volume 0 1 :=
    (continuous_const.mul (continuous_density h)).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun t => foldMoment h t/2) volume 0 1 :=
    ((continuous_foldMoment h).div_const 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi₁ hi₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hl
  have hm := foldMoment_integral_le hh
  apply (le_div_iff₀ (totalMass_pos hh)).mpr
  have he : (Real.log h-Real.log (Real.sqrt (2*Real.pi))-1/(2*totalMass h))*totalMass h =
      (Real.log h-Real.log (Real.sqrt (2*Real.pi)))*totalMass h-1/2 := by
    field_simp [(totalMass_pos hh).ne']
  rw [he]
  dsimp [totalMass] at *
  linarith

lemma logMean_lower_of_half {h : ℝ} (hh : 0 < h) (ha : 1/2 ≤ totalMass h) :
    Real.log h-Real.log (Real.sqrt (2*Real.pi))-1 ≤ logMean h := by
  have hi : 1/(2*totalMass h) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  linarith [logMean_lower hh]



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real


def law (h : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) 1)).withDensity
    (fun t => ENNReal.ofReal (density h t/totalMass h))

lemma measurable_weight (h : ℝ) :
    Measurable (fun t => ENNReal.ofReal (density h t/totalMass h)) :=
  ((continuous_density h).div_const _).measurable.ennreal_ofReal

lemma integral_law {h : ℝ} (hh : 0 < h) (g : ℝ → ℝ) :
    (∫ t, g t ∂law h) = (∫ t in (0 : ℝ)..1, density h t*g t)/totalMass h := by
  unfold law
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_weight h)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (density_pos hh _).le (totalMass_pos hh).le),
    smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div, integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

lemma law_isProbability {h : ℝ} (hh : 0 < h) : IsProbabilityMeasure (law h) := by
  constructor
  unfold law
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div, integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    change ENNReal.ofReal (totalMass h/totalMass h) = 1
    rw [div_self (totalMass_pos hh).ne', ENNReal.ofReal_one]
  · exact ((continuous_density h).div_const _).integrableOn_Icc
  · exact Filter.Eventually.of_forall (fun t =>
      div_nonneg (density_pos hh t).le (totalMass_pos hh).le)

lemma law_ae_mem (h : ℝ) : ∀ᵐ t ∂law h, t ∈ Icc (0 : ℝ) 1 := by
  unfold law
  apply (ae_withDensity_iff (measurable_weight h)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact fun _ => ht

lemma continuous_integrable_law {h : ℝ} (hh : 0 < h) {g : ℝ → ℝ}
    (hg : Continuous g) : Integrable g (law h) := by
  unfold law
  rw [integrable_withDensity_iff (measurable_weight h)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (density_pos hh _).le (totalMass_pos hh).le)]
  exact (hg.mul ((continuous_density h).div_const _)).integrableOn_Icc

lemma continuous_log_density {h : ℝ} (hh : 0 < h) :
    Continuous (fun t => Real.log (density h t)) :=
  (continuous_density h).log (fun t => (density_pos hh t).ne')

lemma integral_log_density {h : ℝ} (hh : 0 < h) :
    (∫ t, Real.log (density h t) ∂law h) = logMean h := integral_law hh _

lemma log_density_bounds {h t : ℝ} (hh : 0 < h) (ht : t ∈ Icc 0 1) :
    Real.log (density h t) ∈ Icc
      (Real.log h-Real.log (Real.sqrt (2*Real.pi))-h^2/8)
      (Real.log h-Real.log (Real.sqrt (2*Real.pi))+Real.log 2) := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)
  constructor
  · have hl := Real.log_le_log (x := h/Real.sqrt (2*Real.pi)*Real.exp (-h^2/8))
      (by positivity) (density_lower hh ht)
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_div hh.ne' hs.ne', Real.log_exp] at hl
    linarith
  · have hu := Real.log_le_log (density_pos hh t) (density_upper hh.le t)
    rw [Real.log_div (mul_pos (by norm_num) hh).ne' hs.ne',
      Real.log_mul (by norm_num) hh.ne'] at hu
    linarith

lemma log_density_memLp {h : ℝ} (hh : 0 < h) :
    MemLp (fun t => Real.log (density h t)) 2 (law h) := by
  let := law_isProbability hh
  refine memLp_of_bounded
    (a := Real.log h-Real.log (Real.sqrt (2*Real.pi))-h^2/8)
    (b := Real.log h-Real.log (Real.sqrt (2*Real.pi))+Real.log 2)
    ?_ (continuous_log_density hh).aestronglyMeasurable 2
  filter_upwards [law_ae_mem h] with t ht
  exact log_density_bounds hh ht

lemma log_density_variance {h : ℝ} (hh : 0 < h) :
    Var[fun t => Real.log (density h t); law h] ≤ ((Real.log 2+h^2/8)/2)^2 := by
  let := law_isProbability hh
  have hb : ∀ᵐ t ∂law h, Real.log (density h t) ∈ Icc
      (Real.log h-Real.log (Real.sqrt (2*Real.pi))-h^2/8)
      (Real.log h-Real.log (Real.sqrt (2*Real.pi))+Real.log 2) := by
    filter_upwards [law_ae_mem h] with t ht
    exact log_density_bounds hh ht
  convert variance_le_sq_of_bounded hb (continuous_log_density hh).measurable.aemeasurable using 1 ; ring



end SingleLatticeCovering.Folded



noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SingleLatticeCovering.Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma chebyshev_real [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ |X ω-∫ x, X x ∂μ|} ≤ Var[X; μ]/c^2 := by
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (meas_ge_le_variance_div_sq hX hc)
  rwa [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg c))] at ht

variable {ι : Type*} [Fintype ι]

lemma sum_memLp [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    MemLp (fun ω : ι → Ω => ∑ i, X (ω i)) 2 (Measure.pi (fun _ : ι => μ)) := by
  exact memLp_finsetSum Finset.univ (fun i _ =>
    hX.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i))

lemma sum_mean [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) :
    (∫ ω : ι → Ω, ∑ i, X (ω i) ∂Measure.pi (fun _ : ι => μ)) =
      (Fintype.card ι : ℝ)*(∫ x, X x ∂μ) := by
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_comp_eval hX)]
  simp only [integral_comp_eval (μ := fun _ : ι => μ) hX.aestronglyMeasurable, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

lemma sum_variance [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[fun ω : ι → Ω => ∑ i, X (ω i); Measure.pi (fun _ : ι => μ)] =
      (Fintype.card ι : ℝ)*Var[X; μ] := by
  have he : (∑ i, fun ω : ι → Ω => X (ω i)) = (fun ω : ι → Ω => ∑ i, X (ω i)) := by
    ext ω; simp
  rw [←he]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    using (variance_sum_pi (μ := fun _ : ι => μ) (X := fun _ : ι => X) (fun _ => hX))

lemma sum_chebyshev [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {v c : ℝ} (hv : Var[X; μ] ≤ v) (hc : 0 < c) :
    (Measure.pi (fun _ : ι => μ)).real
      {ω | c ≤ |(∑ i, X (ω i))-(Fintype.card ι : ℝ)*(∫ x, X x ∂μ)|} ≤
        (Fintype.card ι : ℝ)*v/c^2 := by
  have ht := chebyshev_real (sum_memLp (ι := ι) hX) hc
  rw [sum_mean (hX.integrable (by norm_num)), sum_variance hX] at ht
  exact ht.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
    (sq_nonneg c))

lemma indicator_variance [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s) :
    Var[s.indicator (fun _ => (1 : ℝ)); μ] ≤ μ.real s := by
  have hm : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 μ := (memLp_const 1).indicator hs
  have ht := variance_le_expectation_sq hm.aestronglyMeasurable
  have he : (fun x => (s.indicator (fun _ => (1 : ℝ)) x)^2) = s.indicator (fun _ => (1 : ℝ)) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  change Var[s.indicator (fun _ => (1 : ℝ)); μ] ≤ ∫ x, (s.indicator (fun _ => (1 : ℝ)) x)^2 ∂μ at ht
  rw [he] at ht
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using ht

lemma count_lower_tail [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    (hp : 0 < (Fintype.card ι : ℝ)*μ.real s) :
    (Measure.pi (fun _ : ι => μ)).real
      {ω | (∑ i, s.indicator (fun _ => (1 : ℝ)) (ω i)) <
        (Fintype.card ι : ℝ)*μ.real s/2} ≤ 4/((Fintype.card ι : ℝ)*μ.real s) := by
  have hm : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 μ := (memLp_const 1).indicator hs
  have ht := sum_chebyshev (ι := ι) hm (indicator_variance hs) (half_pos hp)
  simp only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] at ht
  have hsub : {ω : ι → Ω | (∑ i, s.indicator (fun _ => (1 : ℝ)) (ω i)) <
      (Fintype.card ι : ℝ)*μ.real s/2} ⊆
      {ω | (Fintype.card ι : ℝ)*μ.real s/2 ≤
        |(∑ i, s.indicator (fun _ => (1 : ℝ)) (ω i))-(Fintype.card ι : ℝ)*μ.real s|} := by
    intro ω hω
    have hz := le_abs_self (-((∑ i, s.indicator (fun _ => (1 : ℝ)) (ω i))-
      (Fintype.card ι : ℝ)*μ.real s))
    rw [abs_neg] at hz
    dsimp at hω ⊢
    linarith
  have he : (Fintype.card ι : ℝ)*μ.real s/((Fintype.card ι : ℝ)*μ.real s/2)^2 =
      4/((Fintype.card ι : ℝ)*μ.real s) := by field_simp [hp.ne']; ring
  exact (measureReal_mono hsub).trans (ht.trans_eq he)



end SingleLatticeCovering.Concentration


end
end
end
end

end OAI

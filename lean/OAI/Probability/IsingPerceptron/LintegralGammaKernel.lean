import Mathlib
import OAI.Probability.IsingPerceptron.LabeledSampling
import OAI.Probability.IsingPerceptron.MapWithDensityEquiv

namespace OAI

/-! Lintegral Gamma Kernel. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma lintegral_gamma_kernel {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (a-1) * Real.exp (-(s*t)))) =
      ENNReal.ofReal (s ^ (-a) * Real.Gamma a) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (a-1) * Real.exp (-(s*t))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := a-1) (p := 1)
        (by linarith) (by norm_num) hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hs]
    congr 2
    rw [one_div, Real.inv_rpow hs.le, Real.rpow_neg hs.le]
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_nonneg _)

lemma inverse_power_laplace {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    ENNReal.ofReal (s ^ (-a)) =
      (ENNReal.ofReal (Real.Gamma a))⁻¹ *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (a-1) * Real.exp (-(s*t))) := by
  rw [lintegral_gamma_kernel ha hs, ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
  have hG : ENNReal.ofReal (Real.Gamma a) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.Gamma_pos_of_pos ha)).ne'
  rw [mul_left_comm]
  have hGG : (ENNReal.ofReal (Real.Gamma a))⁻¹ * ENNReal.ofReal (Real.Gamma a) = 1 :=
    ENNReal.inv_mul_cancel hG ENNReal.ofReal_ne_top
  rw [hGG, mul_one]

lemma expected_inverse_power {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {T : Ω → ℝ} {F : Ω → ℝ≥0∞}
    (hT : Measurable T) (hF : Measurable F) (hpos : ∀ᵐ ω ∂P, 0 < T ω)
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ ω, ENNReal.ofReal ((T ω) ^ (-a)) * F ω ∂P) =
      (ENNReal.ofReal (Real.Gamma a))⁻¹ * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (a-1)) * ∫⁻ ω, ENNReal.ofReal (Real.exp (-(t*T ω))) * F ω ∂P := by
  have hm : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (p.2 ^ (a-1) * Real.exp (-(T p.1*p.2))) * F p.1) := by
    apply Measurable.mul _ (hF.comp measurable_fst)
    fun_prop
  calc
    _ = ∫⁻ ω, ((ENNReal.ofReal (Real.Gamma a))⁻¹ *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (a-1) * Real.exp (-(T ω*t)))) * F ω ∂P :=
      lintegral_congr_ae (hpos.mono fun ω hω =>
        congrArg (fun x => x * F ω) (inverse_power_laplace ha hω))
    _ = (ENNReal.ofReal (Real.Gamma a))⁻¹ * ∫⁻ ω, (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (a-1) * Real.exp (-(T ω*t))) * F ω) ∂P := by
      have hi (ω : Ω) : (∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (a-1) * Real.exp (-(T ω*t)))) * F ω =
          ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (a-1) * Real.exp (-(T ω*t))) * F ω :=
        (lintegral_mul_const (F ω) (by fun_prop)).symm
      simp_rw [mul_assoc, hi]
      rw [lintegral_const_mul _ (hm.lintegral_prod_right)]
    _ = (ENNReal.ofReal (Real.Gamma a))⁻¹ * ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω,
        ENNReal.ofReal (t ^ (a-1) * Real.exp (-(T ω*t))) * F ω ∂P := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = _ := by
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), mul_assoc]
      rw [lintegral_const_mul]
      · congr 2
        funext ω
        rw [mul_comm (T ω) t]
      · exact (by fun_prop : Measurable (fun ω => ENNReal.ofReal (Real.exp (-(T ω*t))))) |>.mul hF

instance powerIntensity_nullSingleton (b : ℝ) : NullSingletonClass (powerIntensity b) := by
  unfold powerIntensity
  infer_instance

lemma powerIntensity_moment_laplace {b m t : ℝ} (hb : 0 < b) (hmb : b < m) (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal ((max x 0)^m) *
        ENNReal.ofReal (Real.exp (-t * max x 0)) ∂powerIntensity b) =
      ENNReal.ofReal (b * Real.Gamma (m-b) * t^(b-m)) := by
  rw [powerIntensity, lintegral_withDensity_eq_lintegral_mul _
    (measurable_powerIntensityDensity b) (by fun_prop)]
  have he : (fun x => powerIntensityDensity b x *
      (ENNReal.ofReal ((max x 0)^m) * ENNReal.ofReal (Real.exp (-t * max x 0)))) =
      (Ioi (0 : ℝ)).indicator (fun x => ENNReal.ofReal b *
        ENNReal.ofReal (x^((m-b)-1) * Real.exp (-(t*x)))) := by
    funext x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), powerIntensityDensity, ite_eq_left hx, max_eq_left hx.le]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _),
        ← ENNReal.ofReal_mul (mul_nonneg hb.le (Real.rpow_nonneg hx.le _)),
        ← ENNReal.ofReal_mul hb.le]
      congr 1
      calc
        b*x^(-1-b) * (x^m * Real.exp (-t*x)) =
            b * (x^(-1-b)*x^m) * Real.exp (-t*x) := by ring
        _ = b * (x^((m-b)-1) * Real.exp (-(t*x))) := by
          rw [← Real.rpow_add hx, show -1-b+m = (m-b)-1 by ring]
          simp only [neg_mul]
          ring
    · simp only [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), powerIntensityDensity, ite_eq_right hx,
        ENNReal.ofReal_zero, zero_mul]
  simp only [Pi.mul_apply]
  rw [he, lintegral_indicator measurableSet_Ioi, lintegral_const_mul _ (by fun_prop),
    lintegral_gamma_kernel (sub_pos.mpr hmb) ht,
    ← ENNReal.ofReal_mul hb.le]
  congr 1
  rw [show -(m-b) = b-m by ring]
  ring

lemma enegExp_ofReal {x : ℝ} (hx : 0 ≤ x) :
    enegExp (ENNReal.ofReal x) = ENNReal.ofReal (Real.exp (-x)) := by
  rw [← negExp_ofReal hx]
  exact (ENNReal.ofReal_toReal (enegExp_ne_top _)).symm

lemma poissonTotal_enlaplace (b : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ ν, enegExp (ENNReal.ofReal t * poissonTotal ν) ∂poissonLaw (powerIntensity b)) =
      enegExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b) := by
  have h := congrArg ENNReal.ofReal (poissonTotal_laplace b ht)
  have hi : Integrable (fun ν => negExp (ENNReal.ofReal t * poissonTotal ν))
      (poissonLaw (powerIntensity b)) :=
    integrable_negExp _ (show Measurable (fun ν => ENNReal.ofReal t * poissonTotal ν) from
      measurable_const.mul measurable_poissonTotal)
  rw [ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun _ => negExp_nonneg _)] at h
  simpa only [negExp, ENNReal.ofReal_toReal (enegExp_ne_top _)] using h

lemma enegExp_mul_total_ae {b t : ℝ} (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (fun ν => enegExp (ENNReal.ofReal t * poissonTotal ν)) =ᵐ[poissonLaw (powerIntensity b)]
      (fun ν => ENNReal.ofReal (Real.exp (-(t*(poissonTotal ν).toReal)))) := by
  filter_upwards [poissonTotal_finite_positive hb hb1] with ν hν
  rw [← ENNReal.ofReal_toReal hν.2.ne, ← ENNReal.ofReal_mul ht.le,
    enegExp_ofReal (mul_nonneg ht.le ENNReal.toReal_nonneg)]
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

lemma poissonFactorial_power_laplace {b : ℝ} (hb : 0 < b)
    {d k : ℕ} (m : Fin d → ℝ) (hm : ∀ i, b < m i) (z : Fin k → ℝ)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ ν, enegExp (ENNReal.ofReal t * poissonTotal ν) *
        poissonFactorial (powerIntensity b) d
          (fun i x => ENNReal.ofReal ((max x 0)^(m i))) z ν ∂poissonLaw (powerIntensity b)) =
      (∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b))) *
        ENNReal.ofReal (t ^ ((d : ℝ)*b - ∑ i, m i)) *
          enegExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b) := by
  have h := poissonFactorial_laplace (powerIntensity b) d
    (w := fun i x => ENNReal.ofReal ((max x 0)^(m i))) (fun _ => by fun_prop)
    (ψ := fun x => ENNReal.ofReal (t * max x 0)) (by fun_prop) z
  have he (ν : Measure ℝ) : (∫⁻ x, ENNReal.ofReal (t * max x 0) ∂ν) =
      ENNReal.ofReal t * poissonTotal ν := by
    simp only [ENNReal.ofReal_mul ht.le, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      poissonTotal]
  simp only [poissonLaplaceWeight, he] at h
  rw [h, poissonTotal_enlaplace b ht]
  have hi (i : Fin d) : (∫⁻ x, ENNReal.ofReal ((max x 0)^(m i)) *
      enegExp (ENNReal.ofReal (t * max x 0)) ∂powerIntensity b) =
      ENNReal.ofReal (b * Real.Gamma (m i-b)) * ENNReal.ofReal (t^(b-m i)) := by
    have hx (x : ℝ) : enegExp (ENNReal.ofReal (t * max x 0)) =
        ENNReal.ofReal (Real.exp (-t * max x 0)) := by
      simpa only [neg_mul] using enegExp_ofReal (mul_nonneg ht.le (le_max_right x 0))
    simp_rw [hx]
    rw [powerIntensity_moment_laplace hb (hm i) ht,
      ENNReal.ofReal_mul (mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr (hm i))).le)]
  simp_rw [hi]
  rw [Finset.prod_mul_distrib,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg ht.le (b-m i)),
    ← Real.rpow_sum_of_pos ht]
  congr 3
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

def poissonPartitionNumerator (b l : ℝ) {d k : ℕ} (m : Fin d → ℝ) (z : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ ν, ENNReal.ofReal ((poissonTotal ν).toReal ^ (l - ∑ i, m i)) *
    poissonFactorial (powerIntensity b) d (fun i x => ENNReal.ofReal ((max x 0)^(m i))) z ν
      ∂poissonLaw (powerIntensity b)

def partitionCoefficient (b l : ℝ) {d : ℕ} (m : Fin d → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.Gamma ((∑ i, m i)-l)))⁻¹ * ∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b))

def partitionTimeIntegral (b l : ℝ) (d : ℕ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t^((d : ℝ)*b-l-1)) *
    enegExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b)

theorem poissonPartitionNumerator_eq {b l : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {d k : ℕ} (m : Fin d → ℝ) (hm : ∀ i, b < m i) (z : Fin k → ℝ)
    (hl : l < ∑ i, m i) :
    poissonPartitionNumerator b l m z =
      partitionCoefficient b l m * partitionTimeIntegral b l d := by
  have hF : Measurable (fun ν => poissonFactorial (powerIntensity b) d
      (fun i x => ENNReal.ofReal ((max x 0)^(m i))) z ν) :=
    measurable_poissonFactorial_param _ d measurable_id measurable_const (fun _ => by fun_prop)
  rw [poissonPartitionNumerator, show l - ∑ i, m i = -((∑ i, m i)-l) by ring,
    expected_inverse_power _ measurable_poissonTotal.ennreal_toReal hF
      (poissonTotal_real_pos hb hb1) (sub_pos.mpr hl)]
  have hi (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ENNReal.ofReal (t ^ ((∑ i, m i)-l-1)) *
        (∫⁻ ν, ENNReal.ofReal (Real.exp (-(t*(poissonTotal ν).toReal))) *
          poissonFactorial (powerIntensity b) d
            (fun i x => ENNReal.ofReal ((max x 0)^(m i))) z ν ∂poissonLaw (powerIntensity b)) =
      (∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b))) *
        (ENNReal.ofReal (t^((d : ℝ)*b-l-1)) *
          enegExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b)) := by
    have hae := (enegExp_mul_total_ae hb hb1 ht).symm
    have heq := lintegral_congr_ae (hae.mul (ae_eq_refl (fun ν =>
      poissonFactorial (powerIntensity b) d
        (fun i x => ENNReal.ofReal ((max x 0)^(m i))) z ν)))
    simp only [Pi.mul_apply] at heq
    rw [heq, poissonFactorial_power_laplace hb m hm z ht]
    have hp : ENNReal.ofReal (t ^ ((∑ i, m i)-l-1)) *
        ENNReal.ofReal (t^((d : ℝ)*b-∑ i, m i)) =
        ENNReal.ofReal (t^((d : ℝ)*b-l-1)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]
      congr 2
      ring
    calc
      _ = (∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b))) *
          ((ENNReal.ofReal (t ^ ((∑ i, m i)-l-1)) *
            ENNReal.ofReal (t^((d : ℝ)*b-∑ i, m i))) *
            enegExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b)) := by ring
      _ = _ := by rw [hp]
  rw [setLIntegral_congr_fun measurableSet_Ioi hi, lintegral_const_mul]
  · exact (mul_assoc _ _ _).symm
  · exact (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (t^((d : ℝ)*b-l-1)))).mul
      (continuous_enegExp.measurable.comp (by fun_prop))

lemma partitionCoefficient_ofReal {b l : ℝ} (hb : 0 < b) {d : ℕ}
    (m : Fin d → ℝ) (hm : ∀ i, b < m i) (hl : l < ∑ i, m i) :
    partitionCoefficient b l m =
      ENNReal.ofReal ((∏ i, b * Real.Gamma (m i-b)) / Real.Gamma ((∑ i, m i)-l)) := by
  rw [partitionCoefficient,
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg hb.le
      (Real.Gamma_pos_of_pos (sub_pos.mpr (hm i))).le),
    ← ENNReal.ofReal_inv_of_pos (Real.Gamma_pos_of_pos (sub_pos.mpr hl)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.Gamma_pos_of_pos (sub_pos.mpr hl)).le)]
  congr 1
  ring

lemma sum_increment_entry {d : ℕ} (m : Fin d → ℝ) (r : Fin d) :
    (∑ i, Function.update m r (m r+1) i) = (∑ i, m i)+1 := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ r), Finset.sdiff_singleton_eq_erase]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  ring

lemma gamma_product_increment {b : ℝ} {d : ℕ} (m : Fin d → ℝ)
    (hm : ∀ i, b < m i) (r : Fin d) :
    (∏ i, b * Real.Gamma (Function.update m r (m r+1) i-b)) =
      (m r-b) * ∏ i, b * Real.Gamma (m i-b) := by
  classical
  have he : (fun i => b * Real.Gamma (Function.update m r (m r+1) i-b)) =
      Function.update (fun i => b * Real.Gamma (m i-b)) r
        ((m r-b) * (b * Real.Gamma (m r-b))) := by
    funext i
    by_cases hi : i = r
    · subst i
      simp only [Function.update_self, show m r+1-b = (m r-b)+1 by ring,
        Real.Gamma_add_one (sub_pos.mpr (hm r)).ne']
      ring
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ r), Finset.sdiff_singleton_eq_erase]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
  ring

lemma partitionCoefficient_increment {b l : ℝ} (hb : 0 < b) {d : ℕ}
    (m : Fin d → ℝ) (hm : ∀ i, b < m i) (hl : l < ∑ i, m i) (r : Fin d) :
    partitionCoefficient b l (Function.update m r (m r+1)) =
      ENNReal.ofReal ((m r-b)/((∑ i, m i)-l)) * partitionCoefficient b l m := by
  have hmu : ∀ i, b < Function.update m r (m r+1) i := by
    intro i
    by_cases hi : i = r
    · subst i
      rw [Function.update_self]
      linarith [hm r]
    · rw [Function.update_of_ne hi]
      exact hm i
  have hlu : l < ∑ i, Function.update m r (m r+1) i := by
    rw [sum_increment_entry]
    linarith
  rw [partitionCoefficient_ofReal hb _ hmu hlu, partitionCoefficient_ofReal hb m hm hl,
    ← ENNReal.ofReal_mul (div_nonneg (sub_pos.mpr (hm r)).le (sub_pos.mpr hl).le),
    gamma_product_increment m hm r, sum_increment_entry,
    show (∑ i, m i)+1-l = ((∑ i, m i)-l)+1 by ring,
    Real.Gamma_add_one (sub_pos.mpr hl).ne']
  congr 1
  rw [div_mul_eq_div_mul_one_div]
  ring

theorem poissonPartitionNumerator_increment {b l : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {d k : ℕ} (m : Fin d → ℝ) (hm : ∀ i, b < m i) (z : Fin k → ℝ)
    (hl : l < ∑ i, m i) (r : Fin d) :
    poissonPartitionNumerator b l (Function.update m r (m r+1)) z =
      ENNReal.ofReal ((m r-b)/((∑ i, m i)-l)) * poissonPartitionNumerator b l m z := by
  have hmu : ∀ i, b < Function.update m r (m r+1) i := by
    intro i
    by_cases hi : i = r
    · subst i
      rw [Function.update_self]
      linarith [hm r]
    · rw [Function.update_of_ne hi]
      exact hm i
  have hlu : l < ∑ i, Function.update m r (m r+1) i := by
    rw [sum_increment_entry]
    linarith
  rw [poissonPartitionNumerator_eq hb hb1 _ hmu z hlu,
    poissonPartitionNumerator_eq hb hb1 m hm z hl,
    partitionCoefficient_increment hb m hm hl r, mul_assoc]

end IsingPerceptron

namespace IsingPerceptron.Marked

variable {E : Type} [MeasurableSpace E] [Nonempty E]

def PoissonGood (μ : Measure E) [SigmaFinite μ] (ν : Measure E) : Prop :=
  ∀ n, ν (disjointed (spanningSets μ) n) < ∞

lemma poissonGood_ae (μ : Measure E) [SigmaFinite μ] :
    ∀ᵐ ν ∂poissonLaw μ, PoissonGood μ ν := by
  rw [show (fun ν => PoissonGood μ ν) =
    (fun ν => ∀ n, ν (disjointed (spanningSets μ) n) < ∞) from rfl, ae_all_iff]
  intro n
  have hm := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
  apply ae_lt_top (Measure.measurable_coe hm)
  rw [poissonLaw_mean_count μ hm]
  exact ((measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)).ne

omit [Nonempty E] in
lemma sigmaPart_eq_of_good (μ : Measure E) [SigmaFinite μ] {ν : Measure E}
    (hν : PoissonGood μ ν) : sigmaPart μ ν = ν := by
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

omit [Nonempty E] in
lemma PoissonGood.dirac_add {μ : Measure E} [SigmaFinite μ] {ν : Measure E}
    (hν : PoissonGood μ ν) (x : E) : PoissonGood μ (Measure.dirac x + ν) := by
  intro n
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, hν n⟩

def poissonFactorial (μ : Measure E) [SigmaFinite μ] (π : E → ℝ) :
    (d : ℕ) → {m : ℕ} → (Fin d → E → ℝ≥0∞) → (Fin m → ℝ) → Measure E → ℝ≥0∞
  | 0, _, _, _, _ => 1
  | d+1, _, w, z, ν => ∫⁻ x,
      if ∀ j, π x ≠ z j then
        w 0 x * poissonFactorial μ π d (fun i => w i.succ) (Fin.cons (π x) z) ν
      else 0 ∂sigmaPart μ ν

lemma measurable_fin_cons_param {A : Type*} [MeasurableSpace A] {m : ℕ}
    {x : A → ℝ} {z : A → Fin m → ℝ} (hx : Measurable x) (hz : Measurable z) :
    Measurable (fun a => (Fin.cons (x a) (z a) : Fin (m+1) → ℝ)) := by
  apply Measurable.of_eval
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa only [Fin.cons_zero] using hx
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply i).comp hz

omit [Nonempty E] in
lemma measurable_poissonFactorial_param (μ : Measure E) [SigmaFinite μ] {π : E → ℝ} (hπ : Measurable π) (d : ℕ) :
    ∀ {A : Type*} [MeasurableSpace A] {m : ℕ}
      {N : A → Measure E} {z : A → Fin m → ℝ} {w : Fin d → E → ℝ≥0∞},
      Measurable N → Measurable z → (∀ i, Measurable (w i)) →
      Measurable (fun a => poissonFactorial μ π d w (z a) (N a)) := by
  induction d with
  | zero => intros; exact measurable_const
  | succ d ih =>
    intro A _ m N z w hN hz hw
    simp only [poissonFactorial]
    apply measurable_sigmaPart_param μ hN (F := fun p : A × E =>
      if ∀ j, π p.2 ≠ z p.1 j then
        w 0 p.2 * poissonFactorial μ π d (fun i => w i.succ) (Fin.cons (π p.2) (z p.1)) (N p.1)
      else 0)
    have hz' : Measurable (fun p : A × E => (Fin.cons (π p.2) (z p.1) : Fin (m+1) → ℝ)) :=
      measurable_fin_cons_param (hπ.comp measurable_snd) (hz.comp measurable_fst)
    have hf := ih (hN.comp measurable_fst) hz' (fun i => hw i.succ)
    apply ((hw 0).comp measurable_snd |>.mul hf).ite _ measurable_const
    simpa only [Set.ofPred_forall, Set.compl_ofPred, Function.comp_apply] using
      MeasurableSet.iInter fun j =>
        (measurableSet_eq_fun (hπ.comp measurable_snd)
          ((measurable_pi_apply j).comp (hz.comp measurable_fst))).compl

omit [Nonempty E] in
lemma poissonFactorial_dirac_add (μ : Measure E) [SigmaFinite μ] {π : E → ℝ} (hπ : Measurable π) (d : ℕ) :
    ∀ {m : ℕ} {w : Fin d → E → ℝ≥0∞} {z : Fin m → ℝ} {ν : Measure E} {x : E},
      (∀ i, Measurable (w i)) → PoissonGood μ ν → (∃ j, z j = π x) →
      poissonFactorial μ π d w z (Measure.dirac x + ν) = poissonFactorial μ π d w z ν := by
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro m w z ν x hw hν hx
    rw [poissonFactorial, poissonFactorial, sigmaPart_eq_of_good μ (hν.dirac_add x),
      sigmaPart_eq_of_good μ hν, lintegral_add_measure]
    have hzero : (∫⁻ y, if ∀ j, π y ≠ z j then w 0 y *
        poissonFactorial μ π d (fun i => w i.succ) (Fin.cons (π y) z) (Measure.dirac x + ν)
        else 0 ∂Measure.dirac x) = 0 := by
      have hm : Measurable (fun y => if ∀ j, π y ≠ z j then w 0 y *
          poissonFactorial μ π d (fun i => w i.succ) (Fin.cons (π y) z) (Measure.dirac x + ν)
          else 0) := by
        have hf : Measurable (fun y => poissonFactorial μ π d (fun i => w i.succ)
            (Fin.cons (π y) z) (Measure.dirac x + ν)) :=
          measurable_poissonFactorial_param μ hπ d measurable_const
            (measurable_fin_cons_param hπ measurable_const) (fun i => hw i.succ)
        apply ((hw 0).mul hf).ite _ measurable_const
        simpa only [Set.ofPred_forall, Set.compl_ofPred, id_eq, Function.comp_apply] using
          MeasurableSet.iInter fun j : Fin m =>
            (measurableSet_eq_fun hπ (measurable_const (a := z j))).compl
      rw [lintegral_dirac' _ hm]
      obtain ⟨j, hj⟩ := hx
      simp only [ite_eq_right (show ¬ ∀ j, π x ≠ z j from fun h => h j hj.symm)]
    rw [hzero, zero_add]
    apply lintegral_congr
    intro y
    split_ifs with hy
    · congr 1
      apply ih (fun i => hw i.succ) hν
      obtain ⟨j, hj⟩ := hx
      exact ⟨j.succ, by simpa only [Fin.cons_succ] using hj⟩
    · rfl

def poissonLaplaceWeight (ψ : E → ℝ≥0∞) (ν : Measure E) : ℝ≥0∞ :=
  enegExp (∫⁻ x, ψ x ∂ν)

omit [Nonempty E] in
lemma measurable_poissonLaplaceWeight {ψ : E → ℝ≥0∞} (hψ : Measurable ψ) :
    Measurable (poissonLaplaceWeight ψ) :=
  continuous_enegExp.measurable.comp (Measure.measurable_lintegral hψ)

omit [Nonempty E] in
lemma poissonLaplaceWeight_dirac_add {ψ : E → ℝ≥0∞} (hψ : Measurable ψ)
    (x : E) (ν : Measure E) :
    poissonLaplaceWeight ψ (Measure.dirac x + ν) =
      enegExp (ψ x) * poissonLaplaceWeight ψ ν := by
  simp only [poissonLaplaceWeight, lintegral_add_measure, lintegral_dirac' _ hψ, enegExp_add]

omit [Nonempty E] in
lemma measurable_poissonFactorial_body (μ : Measure E) [SigmaFinite μ]
    {π : E → ℝ} (hπ : Measurable π)
    {d m : ℕ} {w : Fin (d+1) → E → ℝ≥0∞} (hw : ∀ i, Measurable (w i))
    (z : Fin m → ℝ) :
    Measurable (fun p : E × Measure E => if ∀ j, π p.1 ≠ z j then
      w 0 p.1 * poissonFactorial μ π d (fun i => w i.succ) (Fin.cons (π p.1) z) p.2 else 0) := by
  have hf : Measurable (fun p : E × Measure E => poissonFactorial μ π d (fun i => w i.succ)
      (Fin.cons (π p.1) z) p.2) :=
    measurable_poissonFactorial_param μ hπ d measurable_snd
      (measurable_fin_cons_param (hπ.comp measurable_fst) measurable_const) (fun i => hw i.succ)
  apply ((hw 0).comp measurable_fst |>.mul hf).ite _ measurable_const
  simpa only [Set.ofPred_forall, Set.compl_ofPred, id_eq, Function.comp_apply] using
    MeasurableSet.iInter fun j : Fin m =>
      (measurableSet_eq_fun (hπ.comp measurable_fst) (measurable_const (a := z j))).compl

lemma poissonFactorial_laplace_step (μ : Measure E) [SigmaFinite μ]
    {π : E → ℝ} (hπ : Measurable π)
    {d m : ℕ} {w : Fin (d+1) → E → ℝ≥0∞} (hw : ∀ i, Measurable (w i))
    {ψ : E → ℝ≥0∞} (hψ : Measurable ψ) (z : Fin m → ℝ) :
    (∫⁻ ν, poissonLaplaceWeight ψ ν * poissonFactorial μ π (d+1) w z ν ∂poissonLaw μ) =
      ∫⁻ x, if ∀ j, π x ≠ z j then
        (w 0 x * enegExp (ψ x)) * ∫⁻ ν, poissonLaplaceWeight ψ ν *
          poissonFactorial μ π d (fun i => w i.succ) (Fin.cons (π x) z) ν ∂poissonLaw μ
      else 0 ∂μ := by
  let G : E × Measure E → ℝ≥0∞ := fun p => poissonLaplaceWeight ψ p.2 *
    (if ∀ j, π p.1 ≠ z j then w 0 p.1 *
      poissonFactorial μ π d (fun i => w i.succ) (Fin.cons (π p.1) z) p.2 else 0)
  have hG : Measurable G :=
    ((measurable_poissonLaplaceWeight hψ).comp measurable_snd).mul
      (measurable_poissonFactorial_body μ hπ hw z)
  have he : (fun ν => poissonLaplaceWeight ψ ν * poissonFactorial μ π (d+1) w z ν) =ᵐ[
      poissonLaw μ] (fun ν => ∫⁻ x, G (x,ν) ∂ν) := by
    filter_upwards [poissonGood_ae μ] with ν hν
    rw [poissonFactorial, sigmaPart_eq_of_good μ hν]
    exact (lintegral_const_mul' _ _ (enegExp_ne_top _)).symm
  rw [lintegral_congr_ae he, poissonLaw_insertion μ hG]
  apply lintegral_congr
  intro x
  by_cases hx : ∀ j, π x ≠ z j
  · simp only [ite_eq_left hx]
    have hae : (fun ν => G (x,Measure.dirac x + ν)) =ᵐ[poissonLaw μ]
        (fun ν => (w 0 x * enegExp (ψ x)) * (poissonLaplaceWeight ψ ν *
          poissonFactorial μ π d (fun i => w i.succ) (Fin.cons (π x) z) ν)) := by
      filter_upwards [poissonGood_ae μ] with ν hν
      dsimp [G]
      rw [ite_eq_left hx, poissonLaplaceWeight_dirac_add hψ,
        poissonFactorial_dirac_add μ hπ d (fun i => hw i.succ) hν ⟨0, Fin.cons_zero ..⟩]
      ring
    rw [lintegral_congr_ae hae, lintegral_const_mul]
    exact (measurable_poissonLaplaceWeight hψ).mul
      (measurable_poissonFactorial_param μ hπ d measurable_id measurable_const (fun i => hw i.succ))
  · simp only [G, ite_eq_right hx, mul_zero, lintegral_zero]

theorem poissonFactorial_laplace (μ : Measure E) [SigmaFinite μ]
    {π : E → ℝ} (hπ : Measurable π) (hdiff : ∀ a, μ {x | π x = a} = 0)
    (d : ℕ) {w : Fin d → E → ℝ≥0∞} (hw : ∀ i, Measurable (w i))
    {ψ : E → ℝ≥0∞} (hψ : Measurable ψ) {m : ℕ} (z : Fin m → ℝ) :
    (∫⁻ ν, poissonLaplaceWeight ψ ν * poissonFactorial μ π d w z ν ∂poissonLaw μ) =
      (∏ i, ∫⁻ x, w i x * enegExp (ψ x) ∂μ) *
        ∫⁻ ν, poissonLaplaceWeight ψ ν ∂poissonLaw μ := by
  induction d generalizing m with
  | zero => simp [poissonFactorial]
  | succ d ih =>
    rw [poissonFactorial_laplace_step μ hπ hw hψ]
    simp_rw [ih (fun i => hw i.succ)]
    have hae : ∀ᵐ x ∂μ, ∀ j, π x ≠ z j := by
      rw [ae_all_iff]
      intro j
      exact ae_iff.mpr (by simpa only [not_not] using hdiff (z j))
    rw [lintegral_congr_ae (hae.mono (fun x hx => ite_eq_left hx))]
    rw [lintegral_mul_const, Fin.prod_univ_succ]
    · ring
    · exact (hw 0).mul (continuous_enegExp.measurable.comp hψ)

end IsingPerceptron.Marked

namespace IsingPerceptron
variable {E : Type} [MeasurableSpace E] [Nonempty E]

def markedPoissonTotal (ν : Measure (ℝ × E)) : ℝ≥0∞ := ∫⁻ p, ENNReal.ofReal (max p.1 0) ∂ν

omit [Nonempty E] in
lemma measurable_markedPoissonTotal : Measurable (markedPoissonTotal (E := E)) :=
  Measure.measurable_lintegral (by fun_prop)

omit [Nonempty E] in
lemma markedPoissonTotal_eq (ν : Measure (ℝ × E)) :
    markedPoissonTotal ν = poissonTotal (ν.map Prod.fst) := by
  rw [poissonTotal, lintegral_map (by fun_prop) measurable_fst]
  rfl

lemma markedPoissonLaw_fst (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ] :
    (poissonLaw ((powerIntensity b).prod μ)).map
      (fun ν => ν.map Prod.fst) = poissonLaw (powerIntensity b) := by
  rw [poissonLaw_map _ measurable_fst]
  have he : ((powerIntensity b).prod μ).map Prod.fst = powerIntensity b := by simp
  exact poissonLaw_congr he

lemma markedPoissonTotal_positive {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    ∀ᵐ ν ∂poissonLaw ((powerIntensity b).prod μ), 0 < (markedPoissonTotal ν).toReal := by
  have h := poissonTotal_real_pos hb hb1
  rw [← markedPoissonLaw_fst b μ] at h
  simpa only [Filter.EventuallyEq, ← markedPoissonTotal_eq] using
    ae_of_ae_map (Measure.measurable_map Prod.fst measurable_fst).aemeasurable h

lemma markedPoissonTotal_enlaplace (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ ν, enegExp (ENNReal.ofReal t * markedPoissonTotal ν)
      ∂poissonLaw ((powerIntensity b).prod μ)) =
      enegExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b) := by
  have h := poissonTotal_enlaplace b ht
  rw [← markedPoissonLaw_fst b μ,
    lintegral_map (show Measurable (fun ν : Measure ℝ =>
      enegExp (ENNReal.ofReal t * poissonTotal ν)) from continuous_enegExp.measurable.comp
        (measurable_const.mul measurable_poissonTotal))
        (Measure.measurable_map Prod.fst measurable_fst)] at h
  simpa only [← markedPoissonTotal_eq] using h

lemma markedPoissonTotal_enegExp_ae {b t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (μ : Measure E) [IsProbabilityMeasure μ] (ht : 0 < t) :
    (fun ν => enegExp (ENNReal.ofReal t * markedPoissonTotal ν)) =ᵐ[
      poissonLaw ((powerIntensity b).prod μ)]
      (fun ν => ENNReal.ofReal (Real.exp (-(t*(markedPoissonTotal ν).toReal)))) := by
  have h := enegExp_mul_total_ae hb hb1 ht
  rw [← markedPoissonLaw_fst b μ] at h
  simpa only [Filter.EventuallyEq, ← markedPoissonTotal_eq] using
    ae_of_ae_map (Measure.measurable_map Prod.fst measurable_fst).aemeasurable h

omit [Nonempty E] in
lemma markedPower_fiber_null (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ] (a : ℝ) :
    ((powerIntensity b).prod μ) {p | p.1 = a} = 0 := by
  have he : {p : ℝ × E | p.1 = a} = ({a} : Set ℝ) ×ˢ (Set.univ : Set E) := by ext p; simp
  rw [he, Measure.prod_prod]
  simp

omit [Nonempty E] in
lemma marked_power_moment_laplace {b m t : ℝ} (hb : 0 < b) (hmb : b < m)
    (μ : Measure E) [IsProbabilityMeasure μ] {F : E → ℝ≥0∞}
    (hF : Measurable F) (ht : 0 < t) : (∫⁻ p : ℝ × E,
      (ENNReal.ofReal ((max p.1 0)^m) * F p.2) *
        enegExp (ENNReal.ofReal (t * max p.1 0)) ∂(powerIntensity b).prod μ) =
      (∫⁻ y, F y ∂μ) * ENNReal.ofReal (b * Real.Gamma (m-b)) *
        ENNReal.ofReal (t^(b-m)) := by
    have hm : Measurable (fun p : ℝ × E =>
        (ENNReal.ofReal ((max p.1 0)^m) * F p.2) * enegExp (ENNReal.ofReal (t * max p.1 0))) :=
      ((by fun_prop : Measurable (fun p : ℝ × E => ENNReal.ofReal ((max p.1 0)^m))).mul
        (hF.comp measurable_snd)).mul (continuous_enegExp.measurable.comp (by fun_prop))
    rw [lintegral_prod _ hm.aemeasurable]
    have hp (x : ℝ) : (∫⁻ y, (ENNReal.ofReal ((max x 0)^m) * F y) *
        enegExp (ENNReal.ofReal (t * max x 0)) ∂μ) =
        (ENNReal.ofReal ((max x 0)^m) *
          enegExp (ENNReal.ofReal (t * max x 0))) * ∫⁻ y, F y ∂μ := by
      simp_rw [mul_right_comm _ (F _)]
      exact lintegral_const_mul _ (hF)
    simp_rw [hp]
    rw [lintegral_mul_const _ (show Measurable (fun x : ℝ =>
      ENNReal.ofReal ((max x 0)^m) * enegExp (ENNReal.ofReal (t*max x 0))) from
        (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal ((max x 0)^m))).mul
          (continuous_enegExp.measurable.comp (by fun_prop)))]
    have hx (x : ℝ) : enegExp (ENNReal.ofReal (t * max x 0)) =
        ENNReal.ofReal (Real.exp (-t * max x 0)) := by
      simpa only [neg_mul] using enegExp_ofReal (mul_nonneg ht.le (le_max_right x 0))
    simp_rw [hx]
    rw [powerIntensity_moment_laplace hb hmb ht,
      ENNReal.ofReal_mul (mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hmb)).le)]
    ring

lemma markedFactorial_power_laplace {b : ℝ} (hb : 0 < b)
    (μ : Measure E) [IsProbabilityMeasure μ] {d k : ℕ}
    (m : Fin d → ℝ) (hm : ∀ i, b < m i) (F : Fin d → E → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) (z : Fin k → ℝ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ ν, enegExp (ENNReal.ofReal t * markedPoissonTotal ν) *
      Marked.poissonFactorial ((powerIntensity b).prod μ) Prod.fst d
        (fun i p => ENNReal.ofReal ((max p.1 0)^(m i)) * F i p.2) z ν
      ∂poissonLaw ((powerIntensity b).prod μ)) =
    ((∏ i, ∫⁻ y, F i y ∂μ) * (∏ i, ENNReal.ofReal (b * Real.Gamma (m i-b)))) *
      ENNReal.ofReal (t ^ ((d : ℝ)*b - ∑ i, m i)) *
        enegExp (ENNReal.ofReal (t^b) * stableLaplaceConstant b) := by
  have h := Marked.poissonFactorial_laplace ((powerIntensity b).prod μ)
    measurable_fst (markedPower_fiber_null b μ) d
    (w := fun i p => ENNReal.ofReal ((max p.1 0)^(m i)) * F i p.2)
    (fun i => (by fun_prop : Measurable (fun p : ℝ × E =>
      ENNReal.ofReal ((max p.1 0)^(m i)))).mul ((hF i).comp measurable_snd))
    (ψ := fun p => ENNReal.ofReal (t * max p.1 0)) (by fun_prop) z
  have he (ν : Measure (ℝ × E)) : (∫⁻ p, ENNReal.ofReal (t * max p.1 0) ∂ν) =
      ENNReal.ofReal t * markedPoissonTotal ν := by
    simp only [ENNReal.ofReal_mul ht.le, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      markedPoissonTotal]
  simp only [Marked.poissonLaplaceWeight, he] at h
  rw [h, markedPoissonTotal_enlaplace b μ ht]
  have hi (i : Fin d) := marked_power_moment_laplace hb (hm i) μ (hF i) ht
  simp_rw [hi, Finset.prod_mul_distrib]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg ht.le (b-m i)),
    ← Real.rpow_sum_of_pos ht]
  congr 3
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

end IsingPerceptron

end

end OAI

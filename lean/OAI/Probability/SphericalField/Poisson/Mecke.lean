import Mathlib
import OAI.Probability.SphericalField.Poisson.PositiveMass

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma poissonMeasure_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r {n+1} * (n+1 : ℝ≥0∞) = (r : ℝ≥0∞) * poissonMeasure r {n} := by
  rw [poissonMeasure_singleton,poissonMeasure_singleton]
  have he : Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / (n+1).factorial * (n+1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp
  have hh := congrArg ENNReal.ofReal he
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-(r : ℝ)) *
    (r : ℝ)^(n+1) / (n+1).factorial), ENNReal.ofReal_mul r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal,ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one,
    ENNReal.ofReal_natCast,ENNReal.ofReal_one] using hh

lemma finitePoissonLaw_mecke {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂finitePoissonLaw r ν) =
      (r : ℝ≥0∞) * ∫⁻ x, ∫⁻ η, H (Measure.dirac x + η,x) ∂finitePoissonLaw r ν ∂ν := by
  rw [finitePoissonLaw,lintegral_sum_measure]
  simp_rw [lintegral_smul_measure]
  have hmap (n : ℕ) :
      (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂(Measure.pi fun _ : Fin n => ν).map (finitePointMeasure n)) =
      ∫⁻ y : Fin n → S, ∫⁻ x, H (finitePointMeasure n y,x) ∂finitePointMeasure n y
        ∂Measure.pi (fun _ => ν) := by
    apply lintegral_map'
    · exact aemeasurable_measure_lintegral_of_finite
        ((ae_map_iff (finitePointMeasure_measurable n).aemeasurable
          (measurableSet_lt (Measure.measurable_coe .univ) measurable_const)).mpr
            (ae_of_all _ fun y => by simp [finitePointMeasure,Measure.finsetSum_apply])) hH
    · exact (finitePointMeasure_measurable n).aemeasurable
  simp_rw [hmap]
  have hinner (n : ℕ) (y : Fin n → S) :
      (∫⁻ x, H (finitePointMeasure n y,x) ∂finitePointMeasure n y) =
        ∑ i, H (finitePointMeasure n y,y i) :=
    finitePointMeasure_lintegral (hH.comp (measurable_const.prodMk measurable_id)) _ _
  simp only [hinner,smul_eq_mul]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Fin.sum_univ_zero,lintegral_zero,mul_zero,zero_add]
  simp_rw [finite_point_mecke ν _ hH,← mul_assoc,poissonMeasure_succ_mul,mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hmn (n : ℕ) : Measurable (fun x : S => ∫⁻ y : Fin n → S,
      H (Measure.dirac x + finitePointMeasure n y,x) ∂Measure.pi (fun _ => ν)) := by
    have hm : Measurable (fun p : S × (Fin n → S) => Measure.dirac p.1 + finitePointMeasure n p.2) := by
      fun_prop
    exact (hH.comp (hm.prodMk measurable_fst)).lintegral_prod_right'
  symm
  calc
    _ = ∫⁻ x, ∑' n : ℕ, poissonMeasure r {n} * ∫⁻ y : Fin n → S,
        H (Measure.dirac x + finitePointMeasure n y,x) ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_congr
      intro x
      rw [lintegral_sum_measure]
      simp only [lintegral_smul_measure,smul_eq_mul]
      apply tsum_congr
      intro n
      congr 1
      exact lintegral_map
        (hH.comp ((measurable_const.add measurable_id).prodMk measurable_const))
        (finitePointMeasure_measurable n)
    _ = _ := by
      rw [lintegral_tsum (f := fun (n : ℕ) (x : S) => poissonMeasure r {n} *
        ∫⁻ y : Fin n → S, H (Measure.dirac x + finitePointMeasure n y,x) ∂Measure.pi (fun _ => ν))
        (fun n => (measurable_const.mul (hmn n)).aemeasurable)]
      apply tsum_congr
      intro n
      exact lintegral_const_mul' _ _ (measure_ne_top _ _)

def stableLaplaceConstant (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1-Real.exp (-Real.exp x)) ∂stableLogIntensity b

lemma one_sub_exp_neg_le_min {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 1-Real.exp (-u) ∧ 1-Real.exp (-u) ≤ min u 1 := by
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu))
  · exact le_min (by linarith [Real.add_one_le_exp (-u)]) (by linarith [Real.exp_pos (-u)])

lemma stableLaplaceConstant_finite {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b ≠ ⊤ := by
  apply ne_top_of_le_ne_top (stableLogIntensity_min_exp_finite hb0 hb1)
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (one_sub_exp_neg_le_min (Real.exp_pos x).le).2

lemma stableLaplaceConstant_positive {b : ℝ} (hb : 0 < b) :
    0 < stableLaplaceConstant b := by
  unfold stableLaplaceConstant
  rw [lintegral_pos_iff_support (by fun_prop)]
  have he : Function.support (fun x : ℝ => ENNReal.ofReal (1-Real.exp (-Real.exp x))) = univ := by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by
      have hh := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos x))
      linarith))
  rw [he,stableLogIntensity_univ hb]
  simp

lemma stableLaplaceExponent_scaling {b t : ℝ} (hb : 0 ≤ b) (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (1-Real.exp (-(t*Real.exp x))) ∂stableLogIntensity b) =
      ENNReal.ofReal (t^b) * stableLaplaceConstant b := by
  have he := stableLogIntensity_lintegral_translate hb (Real.log t)
    (f := fun x => ENNReal.ofReal (1-Real.exp (-Real.exp x))) (by fun_prop)
  have hx (x : ℝ) : Real.exp (x+Real.log t) = t*Real.exp x := by
    rw [Real.exp_add,Real.exp_log ht]
    exact mul_comm _ _
  simp_rw [hx] at he
  convert he using 1
  rw [Real.rpow_def_of_pos ht,mul_comm b (Real.log t)]
  rfl

def stablePoissonTotal (η : Measure ℝ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η).toReal

lemma stablePoissonTotal_measurable : Measurable stablePoissonTotal :=
  ENNReal.measurable_toReal.comp (Measure.measurable_lintegral (by fun_prop))

lemma stablePoissonTotal_pos {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b), 0 < stablePoissonTotal η := by
  filter_upwards [stablePoisson_total_positive hb0,stablePoisson_total_finite hb0 hb1] with η hp hf
  exact ENNReal.toReal_pos hp.ne' hf

lemma stablePoissonTotal_laplace {b t : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (∫ η, Real.exp (-t*stablePoissonTotal η) ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      Real.exp (-(stableLaplaceConstant b).toReal * t^b) := by
  have he := poissonRandomMeasureLaw_laplace (stableLogIntensity b)
    (f := fun x => t*Real.exp x) (by fun_prop) (fun x => mul_nonneg ht.le (Real.exp_pos x).le)
  rw [stableLaplaceExponent_scaling hb0.le ht,
    expNegENNReal_finite (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (stableLaplaceConstant_finite hb0 hb1)),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.rpow_pos_of_pos ht b).le] at he
  convert he using 1
  · apply integral_congr_ae
    filter_upwards [stablePoisson_total_finite hb0 hb1] with η hη
    simp only [poissonLaplace,ENNReal.ofReal_mul ht.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      expNegENNReal_finite (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hη),
      ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le]
    congr 1
    dsimp [stablePoissonTotal]
    ring
  · congr 1
    ring

lemma standardGaussian_integrationByParts {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hm : Measurable F')
    {C D : ℝ} (hb : ∀ x, |F x| ≤ C) (hb' : ∀ x, |F' x| ≤ D) :
    ∫ x, x * F x ∂gaussianReal 0 1 = ∫ x, F' x ∂gaussianReal 0 1 := by
  have hfm : Measurable F := (continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)).measurable
  have h1 : Integrable (fun x => gaussianPDFReal 0 1 x * F' x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb' x)
  have h2 : Integrable (fun x => (-x * gaussianPDFReal 0 1 x) * F x) := by
    have hh := standardGaussian_density_mul_integrable.neg.mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
    simpa only [neg_mul,Pi.neg_apply] using hh
  have h3 : Integrable (fun x => gaussianPDFReal 0 1 x * F x) :=
    (integrable_gaussianPDFReal 0 1).mul_bdd hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => standardGaussian_density_deriv x) (fun x _ => hF x) h1 h2 h3
  simp only [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul]
  rw [he]
  simp only [neg_mul,integral_neg,neg_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

end SphericalPerceptron
end
end

end OAI

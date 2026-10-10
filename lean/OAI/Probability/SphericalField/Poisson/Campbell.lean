import Mathlib
import OAI.Probability.SphericalField.Poisson.RandomMeasure

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma finitePointMeasure_lintegral {S : Type*} [MeasurableSpace S]
    {f : S → ℝ≥0∞} (hf : Measurable f) (n : ℕ) (x : Fin n → S) :
    ∫⁻ a, f a ∂finitePointMeasure n x = ∑ i, f (x i) := by
  simp only [finitePointMeasure,lintegral_finsetSum_measure,lintegral_dirac' _ hf]

lemma finitePoissonLaw_campbell {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ η, ∫⁻ x, f x ∂η ∂finitePoissonLaw r ν = (r : ℝ≥0∞) * ∫⁻ x, f x ∂ν := by
  have hm := Measure.measurable_lintegral hf
  rw [finitePoissonLaw,lintegral_sum_measure]
  simp_rw [lintegral_smul_measure,lintegral_map hm (finitePointMeasure_measurable _),
    finitePointMeasure_lintegral hf]
  have he (n : ℕ) : (∫⁻ x : Fin n → S, ∑ i, f (x i) ∂Measure.pi (fun _ => ν)) =
      (n : ℝ≥0∞) * ∫⁻ y, f y ∂ν := by
    rw [lintegral_finsetSum (f := fun (i : Fin n) (x : Fin n → S) => f (x i)) _
      (fun i _ => hf.comp (measurable_pi_apply i))]
    simp_rw [(measurePreserving_eval (fun _ : Fin n => ν) _).lintegral_comp hf]
    simp
  simp_rw [he,smul_eq_mul,← mul_assoc]
  rw [ENNReal.tsum_mul_right,poissonMeasure_mean]

lemma countablePoissonLaw_campbell {S : Type*} [MeasurableSpace S]
    (r : ℕ → ℝ≥0) (ν : ℕ → Measure S) [∀ i, IsProbabilityMeasure (ν i)]
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ η, ∫⁻ x, f x ∂η ∂countablePoissonLaw r ν =
      ∫⁻ x, f x ∂countablePoissonIntensity r ν := by
  rw [countablePoissonLaw,lintegral_map (Measure.measurable_lintegral hf) measureSum_measurable]
  simp only [lintegral_sum_measure]
  rw [lintegral_tsum (f := fun (i : ℕ) (η : ℕ → Measure S) => ∫⁻ x, f x ∂η i)
    (fun i => ((Measure.measurable_lintegral hf).comp (measurable_pi_apply i)).aemeasurable)]
  simp_rw [(measurePreserving_eval_infinitePi (fun i => finitePoissonLaw (r i) (ν i)) _).lintegral_comp
    (Measure.measurable_lintegral hf),finitePoissonLaw_campbell _ _ hf]
  simp only [countablePoissonIntensity,lintegral_sum_measure,lintegral_smul_measure,smul_eq_mul]

lemma poissonRandomMeasureLaw_campbell {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ η, ∫⁻ x, f x ∂η ∂poissonRandomMeasureLaw κ = ∫⁻ x, f x ∂κ := by
  rw [poissonRandomMeasureLaw,countablePoissonLaw_campbell _ _ hf]
  simp only [countablePoissonIntensity,finiteIntensityMarks_smul,sum_sfiniteSeq]

lemma ae_ne_top_of_laplace_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞} (hZ : Measurable Z)
    (hlim : Tendsto (fun n : ℕ => ∫ ω,
      expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω) ∂P) atTop (𝓝 1)) :
    ∀ᵐ ω ∂P, Z ω ≠ ⊤ := by
  let L : Ω → ℝ := fun ω => if Z ω = ⊤ then 0 else 1
  have hLm : Measurable L := measurable_const.ite (measurableSet_eq_fun hZ measurable_const) measurable_const
  have hLb (ω : Ω) : 0 ≤ L ω ∧ L ω ≤ 1 := by unfold L; split_ifs <;> norm_num
  have hLi : Integrable L P := Integrable.of_bound hLm.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hLb ω).1]; exact (hLb ω).2)
  have hconv (ω : Ω) : Tendsto (fun n : ℕ =>
      expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω)) atTop (𝓝 (L ω)) := by
    by_cases hz : Z ω = ⊤
    · have he (n : ℕ) : expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω) = 0 := by
        rw [hz,ENNReal.mul_top (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))),expNegENNReal_top]
      simpa only [he,L,ite_eq_left hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have he (n : ℕ) : expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω) =
          Real.exp (-(1 / ((n : ℝ)+1) * (Z ω).toReal)) := by
        rw [expNegENNReal_finite (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hz),
          ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
      simp_rw [he]
      simpa [L,hz,Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (Z ω).toReal).neg
  have hconv' := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun n ω => expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) * Z ω))
    (fun _ : Ω => (1 : ℝ))
    (fun n => (expNegENNReal_continuous.measurable.comp
      (measurable_const.mul hZ)).aestronglyMeasurable) (integrable_const 1)
    (fun _ => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (expNegENNReal_bound _).1]
      exact (expNegENNReal_bound _).2) (ae_of_all _ hconv)
  have he : ∫ ω, L ω ∂P = 1 := (tendsto_nhds_unique hlim hconv').symm
  have hzero : ∫ ω, 1 - L ω ∂P = 0 := by rw [integral_sub (integrable_const 1) hLi,he]; simp
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun ω => sub_nonneg.mpr (hLb ω).2) ((integrable_const 1).sub hLi)).mp hzero
  filter_upwards [hae] with ω hω
  intro hz
  simp [L,hz] at hω

lemma poissonRandomMeasureLaw_lintegral_ne_top {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {f : S → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfin : ∫⁻ x, ENNReal.ofReal (min (f x) 1) ∂κ ≠ ⊤) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, (∫⁻ x, ENNReal.ofReal (f x) ∂η) ≠ ⊤ := by
  apply ae_ne_top_of_laplace_tendsto _ (Measure.measurable_lintegral hf.ennreal_ofReal)
  have hf' (n : ℕ) : Measurable (fun x => 1 / ((n : ℝ)+1) * f x) := measurable_const.mul hf
  have hb (n : ℕ) (x : S) : 1 - Real.exp (-(1 / ((n : ℝ)+1) * f x)) ≤ min (f x) 1 := by
    apply le_min
    · have he := Real.add_one_le_exp (-(1 / ((n : ℝ)+1) * f x))
      have hc : 1 / ((n : ℝ)+1) ≤ 1 := by apply (div_le_iff₀ (by positivity)).mpr; simp
      nlinarith [mul_le_of_le_one_left (hf0 x) hc]
    · linarith [Real.exp_pos (-(1 / ((n : ℝ)+1) * f x))]
  have hl := tendsto_lintegral_of_dominated_convergence (μ := κ)
    (F := fun n x => ENNReal.ofReal (1 - Real.exp (-(1 / ((n : ℝ)+1) * f x))))
    (fun x => ENNReal.ofReal (min (f x) 1))
    (fun n => (measurable_const.sub (hf' n).neg.exp).ennreal_ofReal)
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (hb n x)) hfin
    (f := fun _ => 0) (ae_of_all _ fun x => by
      simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (Real.continuous_exp.continuousAt.tendsto.comp
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (f x)).neg)))
  have he (n : ℕ) : (∫ η, expNegENNReal (ENNReal.ofReal (1 / ((n : ℝ)+1)) *
        ∫⁻ x, ENNReal.ofReal (f x) ∂η) ∂poissonRandomMeasureLaw κ) =
      expNegENNReal (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-(1 / ((n : ℝ)+1) * f x))) ∂κ) := by
    convert poissonRandomMeasureLaw_laplace κ (hf' n) (fun x => mul_nonneg (by positivity) (hf0 x)) using 1
    congr 1
    funext η
    unfold poissonLaplace
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (by positivity)]
  simp_rw [he]
  simpa only [lintegral_zero,expNegENNReal_finite (by simp : (0 : ℝ≥0∞) ≠ ⊤),
    ENNReal.toReal_zero,neg_zero,Real.exp_zero,Function.comp_def] using
    expNegENNReal_continuous.continuousAt.tendsto.comp hl

lemma stableLogIntensity_min_exp_finite {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    (∫⁻ x, ENNReal.ofReal (min (Real.exp x) 1) ∂stableLogIntensity b) ≠ ⊤ := by
  have hi : Integrable (fun x : ℝ => b * Real.exp (-b*x) * min (Real.exp x) 1) := by
    have hh := (((integrableOn_exp_mul_Iic (a := 1-b) (by linarith) 0).integrable_indicator
      measurableSet_Iic).add ((integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0).integrable_indicator
      measurableSet_Ioi)).const_mul b
    convert hh using 1
    funext x
    by_cases hx : x ≤ 0
    · simp only [Pi.add_apply]
      rw [indicator_of_mem (show x ∈ Iic 0 from hx),
        indicator_of_notMem (show x ∉ Ioi 0 from not_lt.mpr hx),add_zero,
        min_eq_left (Real.exp_le_one_iff.mpr hx)]
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    · have hx' : 0 < x := lt_of_not_ge hx
      simp only [Pi.add_apply]
      rw [indicator_of_notMem (show x ∉ Iic 0 from hx),
        indicator_of_mem (show x ∈ Ioi 0 from hx'),zero_add,
        min_eq_right (Real.one_le_exp_iff.mpr hx'.le),mul_one]
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) (by fun_prop)]
  have he : (∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x)) * ENNReal.ofReal (min (Real.exp x) 1)) =
      ∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x) * min (Real.exp x) 1) := by
    apply lintegral_congr
    intro x
    exact (ENNReal.ofReal_mul (mul_nonneg hb0.le (Real.exp_pos _).le)).symm
  change (∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x)) * ENNReal.ofReal (min (Real.exp x) 1)) ≠ ⊤
  rw [he]
  exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)).mp hi.hasFiniteIntegral).ne

lemma stablePoisson_total_finite {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b),
      (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η) ≠ ⊤ :=
  poissonRandomMeasureLaw_lintegral_ne_top _ Real.measurable_exp (fun x => (Real.exp_pos x).le)
    (stableLogIntensity_min_exp_finite hb0 hb1)

lemma stableLogIntensity_univ {b : ℝ} (hb : 0 < b) : stableLogIntensity b univ = ⊤ := by
  have ha : (volume : Measure ℝ) ≪ stableLogIntensity b :=
    withDensity_absolutelyContinuous' (by fun_prop)
      (ae_of_all _ fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hb (Real.exp_pos _))))
  have hne : stableLogIntensity b univ ≠ 0 := by
    intro h
    have hh := ha h
    simp at hh
  by_contra ht
  have hs := congrArg (fun κ : Measure ℝ => κ univ) (stableLogIntensity_translate hb.le 1)
  rw [Measure.map_apply (show Measurable (fun x : ℝ => x+1) from measurable_id.add_const 1)
    .univ,preimage_univ,Measure.smul_apply,smul_eq_mul] at hs
  have hr := congrArg ENNReal.toReal hs
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,mul_one] at hr
  have hp := ENNReal.toReal_pos hne ht
  have he : 1 < Real.exp b := Real.one_lt_exp_iff.mpr hb
  nlinarith

end SphericalPerceptron
end
end

end OAI

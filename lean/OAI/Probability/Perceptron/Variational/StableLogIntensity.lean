import Mathlib
import OAI.Probability.Perceptron.Cascade.PoissonLaplace

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma poissonLaplace_map {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {g : S → T} (hg : Measurable g) {f : T → ℝ} (hf : Measurable f) (η : Measure S) :
    poissonLaplace f (η.map g) = poissonLaplace (f ∘ g) η := by
  rw [poissonLaplace,lintegral_map hf.ennreal_ofReal hg]
  rfl

lemma poissonRandomMeasureLaw_map {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [Nonempty S] [Nonempty T] (κ : Measure S) [SFinite κ]
    {g : S → T} (hg : Measurable g) :
    (poissonRandomMeasureLaw κ).map (Measure.map g) = poissonRandomMeasureLaw (κ.map g) := by
  apply measureLaw_eq_of_laplace
  intro f hf hf0
  rw [integral_map (Measure.measurable_map g hg).aemeasurable
    (poissonLaplace_measurable hf).aestronglyMeasurable]
  simp_rw [poissonLaplace_map hg hf]
  rw [poissonRandomMeasureLaw_laplace _ (hf.comp hg) (fun x => hf0 (g x)),
    poissonRandomMeasureLaw_laplace _ hf hf0,
    lintegral_map (show Measurable (fun x : T => ENNReal.ofReal (1 - Real.exp (-f x))) from
      (measurable_const.sub hf.neg.exp).ennreal_ofReal) hg]
  rfl

def stableLogIntensity (b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (b * Real.exp (-b*x)))

instance stableLogIntensity_sigmaFinite (b : ℝ) : SigmaFinite (stableLogIntensity b) := by
  unfold stableLogIntensity
  infer_instance

lemma stableLogDensity_translate {b : ℝ} (_hb : 0 ≤ b) (c x : ℝ) :
    ENNReal.ofReal (b * Real.exp (-b*x)) =
      ENNReal.ofReal (Real.exp (b*c)) * ENNReal.ofReal (b * Real.exp (-b*(x+c))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [mul_left_comm,← Real.exp_add]
  congr 2
  ring

lemma stableLogIntensity_lintegral_translate {b : ℝ} (hb : 0 ≤ b)
    (c : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (x+c) ∂stableLogIntensity b =
      ENNReal.ofReal (Real.exp (b*c)) * ∫⁻ x, f x ∂stableLogIntensity b := by
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) (show Measurable (fun x : ℝ => f (x+c)) from hf.comp (measurable_id.add_const c)),
    lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) hf]
  change (∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x)) * f (x+c)) = _
  calc
    (∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*x)) * f (x+c)) =
        ∫⁻ x, ENNReal.ofReal (Real.exp (b*c)) *
          (ENNReal.ofReal (b * Real.exp (-b*(x+c))) * f (x+c)) := by
      apply lintegral_congr
      intro x
      rw [stableLogDensity_translate hb c x,mul_assoc]
    _ = ENNReal.ofReal (Real.exp (b*c)) *
        ∫⁻ x, ENNReal.ofReal (b * Real.exp (-b*(x+c))) * f (x+c) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      congr 1
      exact lintegral_add_right_eq_self
        (fun x => ENNReal.ofReal (b * Real.exp (-b*x)) * f x) c

lemma stableLogIntensity_translate {b : ℝ} (hb : 0 ≤ b) (c : ℝ) :
    (stableLogIntensity b).map (fun x => x+c) =
      ENNReal.ofReal (Real.exp (b*c)) • stableLogIntensity b := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (show Measurable (fun x : ℝ => x+c) from measurable_id.add_const c),lintegral_smul_measure]
  exact stableLogIntensity_lintegral_translate hb c hf

def logMarkShift {S : Type*} (F : S → ℝ) (p : ℝ × S) : ℝ × S :=
  (p.1 + F p.2,p.2)

lemma logMarkShift_measurable {S : Type*} [MeasurableSpace S]
    {F : S → ℝ} (hF : Measurable F) : Measurable (logMarkShift F) :=
  (measurable_fst.add (hF.comp measurable_snd)).prodMk measurable_snd

lemma stableLogIntensity_mark_shift {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [SFinite ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F) :
    ((stableLogIntensity b).prod ν).map (logMarkShift F) =
      (stableLogIntensity b).prod (ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b * F s)))) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (logMarkShift_measurable hF)]
  rw [lintegral_prod_symm (fun p : ℝ × S => f (logMarkShift F p))
    (show AEMeasurable (fun p : ℝ × S => f (logMarkShift F p)) _ from
      (hf.comp (logMarkShift_measurable hF)).aemeasurable),
    lintegral_prod_symm _ hf.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul ν (by fun_prop)
    (Measurable.lintegral_prod_left' hf)]
  apply lintegral_congr
  intro s
  exact stableLogIntensity_lintegral_translate hb (F s) (hf.comp (measurable_id.prodMk measurable_const))

lemma stablePoisson_mark_shift {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [SFinite ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map (Measure.map (logMarkShift F)) =
      poissonRandomMeasureLaw ((stableLogIntensity b).prod
        (ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b * F s))))) := by
  rw [poissonRandomMeasureLaw_map _ (logMarkShift_measurable hF)]
  congr 1
  exact stableLogIntensity_mark_shift ν hb hF

lemma poissonMeasure_atom_succ (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r {n+1} * (n+1 : ℝ≥0∞) = (r : ℝ≥0∞) * poissonMeasure r {n} := by
  have he : Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / (n+1).factorial * (n+1 : ℝ) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  have he' := congrArg ENNReal.ofReal he
  have hcast : ENNReal.ofReal ((n : ℝ)+1) = (n : ℝ≥0∞)+1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_natCast,ENNReal.ofReal_one]
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / (n+1).factorial),
    ENNReal.ofReal_mul r.coe_nonneg,ENNReal.ofReal_coe_nnreal,hcast,poissonMeasure_singleton] using he'

lemma poissonMeasure_mean (r : ℝ≥0) :
    ∑' n : ℕ, poissonMeasure r {n} * (n : ℝ≥0∞) = r := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero,mul_zero,zero_add,Nat.cast_add,Nat.cast_one]
  simp_rw [poissonMeasure_atom_succ]
  rw [ENNReal.tsum_mul_left]
  have hmass : ∑' n : ℕ, poissonMeasure r {n} = 1 := by
    simp_rw [poissonMeasure_singleton]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
      (hasSum_one_poissonMeasure r).summable,(hasSum_one_poissonMeasure r).tsum_eq]
    norm_num
  rw [hmass,mul_one]

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

lemma poissonRandomMeasureLaw_lintegral_pos_of_infinite {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] (hκ : κ univ = ⊤)
    {f : S → ℝ} (hf : Measurable f) (hfpos : ∀ x, 0 < f x) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, 0 < ∫⁻ x, ENNReal.ofReal (f x) ∂η := by
  have hconst : Measurable (fun _ : S => (1 : ℝ)) := measurable_const
  have he := poissonRandomMeasureLaw_laplace κ hconst (fun _ => zero_le_one)
  have hc : ENNReal.ofReal (1 - Real.exp (-1)) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  rw [lintegral_const,hκ,ENNReal.mul_top hc,expNegENNReal_top] at he
  have hi : Integrable (poissonLaplace (fun _ : S => (1 : ℝ))) (poissonRandomMeasureLaw κ) := by
    apply Integrable.of_bound (poissonLaplace_measurable hconst).aestronglyMeasurable 1
    exact ae_of_all _ fun η => by
      rw [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds _ η).1]
      exact (poissonLaplace_bounds _ η).2
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun η => (poissonLaplace_bounds (fun _ : S => (1 : ℝ)) η).1) hi).mp he
  filter_upwards [hae] with η hη
  have hsp : Function.support (fun x => ENNReal.ofReal (f x)) = univ := by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hfpos x))
  rw [lintegral_pos_iff_support hf.ennreal_ofReal,hsp]
  by_contra hn
  have hz : η univ = 0 := bot_unique (le_of_not_gt hn)
  simp only [poissonLaplace,lintegral_const,ENNReal.ofReal_one,one_mul,hz,
    expNegENNReal_finite (by simp : (0 : ℝ≥0∞) ≠ ⊤),ENNReal.toReal_zero,neg_zero,Real.exp_zero] at hη
  exact one_ne_zero hη

lemma stablePoisson_total_positive {b : ℝ} (hb : 0 < b) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b),
      0 < ∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η :=
  poissonRandomMeasureLaw_lintegral_pos_of_infinite _ (stableLogIntensity_univ hb)
    Real.measurable_exp Real.exp_pos

lemma standardGaussian_density_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hd := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert! hd using 1
  · funext y
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,Pi.neg_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat]
    norm_num
    ring

lemma standardGaussian_density_mul_integrable :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  funext x
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [show -(x ^ 2) / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
  ring

def finiteMeasureCutKernel {S : Type*} [MeasurableSpace S] (n : ℕ) : Kernel (Measure S) S where
  toFun η := if η univ ≤ n then η else 0
  measurable' := measurable_id.piecewise
    (measurableSet_le (Measure.measurable_coe .univ) measurable_const) measurable_const

instance finiteMeasureCutKernel_finite {S : Type*} [MeasurableSpace S] (n : ℕ) :
    IsFiniteKernel (finiteMeasureCutKernel (S := S) n) := by
  refine ⟨n,by simp,fun η => ?_⟩
  change (if η univ ≤ n then η else 0) univ ≤ n
  split_ifs with h
  · exact h
  · simp

lemma aemeasurable_measure_lintegral_of_finite {S : Type*} [MeasurableSpace S]
    {P : Measure (Measure S)} (hP : ∀ᵐ η ∂P, η univ < ⊤)
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    AEMeasurable (fun η => ∫⁻ x, H (η,x) ∂η) P := by
  have hm : Measurable (fun η => ⨆ n : ℕ, ∫⁻ x, H (η,x) ∂finiteMeasureCutKernel n η) :=
    Measurable.iSup fun n => hH.lintegral_kernel_prod_right' (κ := finiteMeasureCutKernel n)
  apply hm.aemeasurable.congr
  filter_upwards [hP] with η hη
  apply le_antisymm
  · apply iSup_le
    intro n
    change (∫⁻ x, H (η,x) ∂(if η univ ≤ n then η else 0)) ≤ _
    split_ifs <;> simp
  · obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hη.ne
    calc
      (∫⁻ x, H (η,x) ∂η) = ∫⁻ x, H (η,x) ∂finiteMeasureCutKernel n η := by
        change _ = ∫⁻ x, H (η,x) ∂(if η univ ≤ n then η else 0)
        rw [ite_eq_left hn.le]
      _ ≤ _ := le_iSup (fun m : ℕ => ∫⁻ x, H (η,x) ∂finiteMeasureCutKernel m η) n

lemma finitePoissonLaw_ae_finite {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) :
    ∀ᵐ η ∂finitePoissonLaw r ν, η univ < ⊤ := by
  rw [finitePoissonLaw,Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure
  rw [ae_map_iff (finitePointMeasure_measurable n).aemeasurable
    (measurableSet_lt (Measure.measurable_coe .univ) measurable_const)]
  exact ae_of_all _ fun x => by simp [finitePointMeasure,Measure.finsetSum_apply]

end SphericalPerceptronFreeEnergy
end

end OAI

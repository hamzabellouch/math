import Mathlib
import OAI.Probability.Perceptron.Variational.BoundedC1

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

def StableCascade : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (Measure (ℝ×StableCascade n))

instance stableCascadeNonempty (n : ℕ) : Nonempty (StableCascade n) := by
  cases n with
  | zero => exact ⟨()⟩
  | succ n => exact ⟨(0 : Measure (ℝ×StableCascade n))⟩

def cascadeTotalE : (n : ℕ) → StableCascade n → ℝ≥0∞
  | 0, _ => 1
  | n+1, η => ∫⁻ p : ℝ×StableCascade n,
      ENNReal.ofReal (Real.exp p.1)*cascadeTotalE n p.2 ∂η

lemma cascadeTotalE_measurable (n : ℕ) : Measurable (cascadeTotalE n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measure.measurable_lintegral
      ((Real.measurable_exp.comp measurable_fst).ennreal_ofReal.mul (ih.comp measurable_snd))

def cascadeTotal (n : ℕ) (η : StableCascade n) : ℝ := (cascadeTotalE n η).toReal

lemma cascadeTotal_measurable (n : ℕ) : Measurable (cascadeTotal n) :=
  (cascadeTotalE_measurable n).ennreal_toReal

def cascadeLaw : (n : ℕ) → (Fin n → ℝ) → ProbabilityMeasure (StableCascade n)
  | 0, _ => ⟨Measure.dirac (),by exact Measure.dirac.isProbabilityMeasure⟩
  | n+1, z => ⟨poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod
      (cascadeLaw n (fun i => z i.succ) : Measure (StableCascade n))),by exact poissonRandomMeasureLaw_probability _⟩

lemma poissonWeightedTotal_identDistrib {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 < b)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    IdentDistrib (poissonWeightedTotal X)
      (fun η => Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b)*stablePoissonTotal η)
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
  ⟨(poissonWeightedTotal_measurable hX).aemeasurable,
    (stablePoissonTotal_measurable.const_mul _).aemeasurable,
    poissonWeightedTotal_law ν hb hX hI⟩

lemma poissonWeightedTotal_pos {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν), 0 < poissonWeightedTotal X η := by
  apply (poissonWeightedTotal_identDistrib ν hb hX hI).symm.ae_snd measurableSet_Ioi
  filter_upwards [stablePoissonTotal_pos hb hb1] with η hη
  exact mul_pos (Real.exp_pos _) hη

lemma poissonWeightedTotal_rpow_integrable {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b a : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    Integrable (fun η => (poissonWeightedTotal X η)^a)
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) := by
  have hid := (poissonWeightedTotal_identDistrib ν hb hX hI).comp
    (measurable_id.pow_const a : Measurable (fun x : ℝ => x^a))
  apply hid.integrable_iff.mpr
  have he (η : Measure ℝ) : (Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b)*stablePoissonTotal η)^a =
      (Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b))^a*(stablePoissonTotal η)^a :=
    Real.mul_rpow (Real.exp_pos _).le ENNReal.toReal_nonneg
  simpa only [Function.comp_def,id_eq,he] using (stablePoissonTotal_rpow_integrable hb hb1 ha).const_mul
    ((Real.exp (Real.log (∫ x, Real.exp (b*X x) ∂ν)/b))^a)

lemma poissonRandomMeasureLaw_ae_ae {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {p : S → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ x ∂κ, p x) : ∀ᵐ η ∂poissonRandomMeasureLaw κ, ∀ᵐ x ∂η, p x := by
  have hh := poissonRandomMeasureLaw_ae_null κ hp.compl (ae_iff.mp h)
  exact hh.mono fun η hη => ae_iff.mpr hη

lemma cascadeTotal_succ_eq {n : ℕ} (z : Fin (n+1) → ℝ)
    (hp : ∀ᵐ η ∂(cascadeLaw n (fun i => z i.succ) : Measure (StableCascade n)),
      0 < cascadeTotal n η) :
    ∀ᵐ η ∂(cascadeLaw (n+1) z : Measure (StableCascade (n+1))),
      cascadeTotal (n+1) η = poissonWeightedTotal (fun C => Real.log (cascadeTotal n C)) η := by
  let ν : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
  have hpκ : ∀ᵐ p ∂(stableLogIntensity (z 0)).prod ν, 0 < cascadeTotal n p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const ((cascadeTotal_measurable n).comp measurable_snd))).mpr
      (ae_of_all _ fun _ => hp)
  have he := poissonRandomMeasureLaw_ae_ae ((stableLogIntensity (z 0)).prod ν)
    (measurableSet_lt measurable_const ((cascadeTotal_measurable n).comp measurable_snd)) hpκ
  change ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod ν), _
  filter_upwards [he] with η hη
  unfold cascadeTotal poissonWeightedTotal
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hη] with p hp
  change ENNReal.ofReal (Real.exp p.1)*cascadeTotalE n p.2 =
    ENNReal.ofReal (Real.exp (p.1+Real.log (cascadeTotal n p.2)))
  change 0 < cascadeTotal n p.2 at hp
  rw [Real.exp_add,Real.exp_log hp,ENNReal.ofReal_mul (Real.exp_pos _).le,cascadeTotal,
    ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.mp hp).2.ne]

theorem cascadeTotal_regular (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    (∀ᵐ η ∂(cascadeLaw n z : Measure (StableCascade n)), 0 < cascadeTotal n η) ∧
    ∀ a : ℝ, (∀ i, a < z i) → Integrable (fun η => (cascadeTotal n η)^a)
      (cascadeLaw n z : Measure (StableCascade n)) := by
  induction n with
  | zero =>
    constructor
    · exact ae_of_all _ fun _ => by simp [cascadeTotal,cascadeTotalE]
    · intro a _; simpa only [cascadeTotal,cascadeTotalE,ENNReal.toReal_one,Real.one_rpow] using
        (integrable_const (1:ℝ) : Integrable (fun _ : StableCascade 0 => (1:ℝ)) (cascadeLaw 0 z : Measure (StableCascade 0)))
  | succ n ih =>
    let ν : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
    have htail : StrictMono (fun i : Fin n => z i.succ) := fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)
    obtain ⟨hpos,hint⟩ := ih (fun i => z i.succ) htail (fun i => hz0 i.succ) (fun i => hz1 i.succ)
    have hM : Integrable (fun C => Real.exp (z 0*Real.log (cascadeTotal n C))) ν := by
      have hh := hint (z 0) (fun i => hz (by simp))
      apply hh.congr
      filter_upwards [hpos] with C hC
      rw [Real.rpow_def_of_pos hC]
      congr 1
      ring
    have hEq := cascadeTotal_succ_eq z hpos
    have hlog : Measurable (fun C : StableCascade n => Real.log (cascadeTotal n C)) :=
      (cascadeTotal_measurable n).log
    constructor
    · have hp := poissonWeightedTotal_pos ν (hz0 0) (hz1 0) hlog hM
      filter_upwards [hp,hEq] with η hp he
      rwa [he]
    · intro a ha
      have hI := poissonWeightedTotal_rpow_integrable ν (hz0 0) (hz1 0) (ha 0) hlog hM
      exact hI.congr (hEq.mono fun η he => congrArg (fun t : ℝ => t^a) he.symm)

lemma lintegral_comp_exp_all (g : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp x)*g (Real.exp x)) = ∫⁻ y : ℝ in Ioi 0, g y := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x (_ : x ∈ (univ : Set ℝ)) => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g
  simpa only [image_univ,Real.range_exp,Measure.restrict_univ,abs_of_pos (Real.exp_pos _)] using h.symm

lemma stableLogIntensity_laplace_moment {b r t : ℝ} (hb : 0 ≤ b) (hr : b < r) (ht : 0 < t) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x)) ∂stableLogIntensity b) =
      ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)) := by
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  have he (x : ℝ) :
      ENNReal.ofReal (b*Real.exp (-b*x))*ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x)) =
      ENNReal.ofReal b*(ENNReal.ofReal (Real.exp x)*
        ENNReal.ofReal ((Real.exp x)^(r-b-1)*Real.exp (-t*Real.exp x))) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hb (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_mul hb]
    congr 1
    rw [← Real.exp_mul]
    have hx : Real.exp (-b*x)*Real.exp (r*x) = Real.exp x*Real.exp (x*(r-b-1)) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    calc
      b*Real.exp (-b*x)*(Real.exp (r*x)*Real.exp (-t*Real.exp x)) =
          b*(Real.exp (-b*x)*Real.exp (r*x))*Real.exp (-t*Real.exp x) := by ring
      _ = _ := by rw [hx]; ring
  change (∫⁻ x : ℝ, ENNReal.ofReal (b*Real.exp (-b*x))*ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))) = _
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_exp_all (fun y : ℝ => ENNReal.ofReal (y^(r-b-1)*Real.exp (-t*y))),
    show (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (y^(r-b-1)*Real.exp (-t*y))) =
      ENNReal.ofReal (t^(-(r-b))*Real.Gamma (r-b)) from by
        simpa only [neg_mul,mul_comm t] using gamma_lintegral_positive_scale (sub_pos.mpr hr) ht,
    ← ENNReal.ofReal_mul hb]
  congr 1
  rw [neg_sub]
  ring

lemma one_sub_exp_neg_lintegral {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (1-Real.exp (-u)) =
      ∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (u*Real.exp (-t*u)) := by
  have hi : IntegrableOn (fun t : ℝ => u*Real.exp (-t*u)) (Ioc 0 1) :=
    (show Continuous (fun t : ℝ => u*Real.exp (-t*u)) by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => mul_nonneg hu.le (Real.exp_pos _).le)]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => -Real.exp (-s*u)) (u*Real.exp (-t*u)) t := by
    convert! (((hasDerivAt_id t).neg.mul_const u).exp).neg using 1
    simp only [Pi.neg_apply,id_eq,one_mul,neg_mul,mul_neg,neg_neg]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => u*Real.exp (-t*u)) by fun_prop).intervalIntegrable 0 1)]
  simp only [neg_mul,zero_mul,neg_zero,Real.exp_zero]
  ring_nf

lemma lintegral_rpow_unit {b : ℝ} (hb : 0 < b) :
    (∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (t^(b-1))) = ENNReal.ofReal b⁻¹ := by
  have hi : IntegrableOn (fun t : ℝ => t^(b-1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith : -1 < b-1)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _),← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_rpow (Or.inl (by linarith : -1 < b-1))]
  simp [Real.zero_rpow hb.ne']

lemma stableLaplaceConstant_eq_gamma {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b = ENNReal.ofReal (Real.Gamma (1-b)) := by
  unfold stableLaplaceConstant
  simp_rw [one_sub_exp_neg_lintegral (Real.exp_pos _)]
  rw [lintegral_lintegral_swap (by fun_prop : Measurable (fun p : ℝ×ℝ =>
    ENNReal.ofReal (Real.exp p.1*Real.exp (-p.2*Real.exp p.1)))).aemeasurable]
  have he : (∫⁻ t : ℝ in Ioc 0 1, ∫⁻ x : ℝ,
      ENNReal.ofReal (Real.exp x*Real.exp (-t*Real.exp x)) ∂stableLogIntensity b) =
      ∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (b*t^(b-1)*Real.Gamma (1-b)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [one_mul] using stableLogIntensity_laplace_moment hb.le hb1 ht.1
  rw [he]
  have hG : 0 ≤ Real.Gamma (1-b) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hf (t : ℝ) : ENNReal.ofReal (b*t^(b-1)*Real.Gamma (1-b)) =
      ENNReal.ofReal (b*Real.Gamma (1-b))*ENNReal.ofReal (t^(b-1)) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hb.le hG)]
    congr 1
    ring
  simp_rw [hf]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_rpow_unit hb,
    ← ENNReal.ofReal_mul (mul_nonneg hb.le hG)]
  congr 1
  field_simp

attribute [fun_prop] stablePoissonTotal_measurable

lemma stablePoissonTotal_add_dirac (x : ℝ) (η : Measure ℝ)
    (hη : (∫⁻ y, ENNReal.ofReal (Real.exp y) ∂η) ≠ ⊤) :
    stablePoissonTotal (Measure.dirac x+η) = Real.exp x+stablePoissonTotal η := by
  unfold stablePoissonTotal
  rw [lintegral_add_measure,lintegral_dirac,
    ENNReal.toReal_add ENNReal.ofReal_ne_top hη,ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma stablePoissonTotal_laplace_lintegral {b t : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (∫⁻ η, ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  have hi : Integrable (fun η => Real.exp (-t*stablePoissonTotal η))
      (poissonRandomMeasureLaw (stableLogIntensity b)) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun η => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le)
        ENNReal.toReal_nonneg)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le),
    stablePoissonTotal_laplace hb hb1 ht,stableLaplaceConstant_eq_gamma hb hb1,
    ENNReal.toReal_ofReal (Real.Gamma_pos_of_pos (by linarith)).le]

lemma stablePoisson_palm_laplace {b r t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hr : b < r) (ht : 0 < t) :
    (∫⁻ η, ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*stablePoissonTotal η))
      ∂η ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)*Real.exp (-Real.Gamma (1-b)*t^b)) := by
  rw [poissonRandomMeasureLaw_mecke (stableLogIntensity b) (by fun_prop : Measurable
    (fun p : Measure ℝ×ℝ => ENNReal.ofReal (Real.exp (r*p.2)*Real.exp (-t*stablePoissonTotal p.1))))]
  have he (x : ℝ) :
      (∫⁻ η, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*stablePoissonTotal (Measure.dirac x+η)))
        ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))*
        ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
    calc
      _ = ∫⁻ η, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))*
          ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
          ∂poissonRandomMeasureLaw (stableLogIntensity b) := by
        apply lintegral_congr_ae
        filter_upwards [stablePoisson_total_finite hb hb1] with η hη
        rw [stablePoissonTotal_add_dirac x η hη,mul_add,Real.exp_add,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
        congr 1
        ring
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,stablePoissonTotal_laplace_lintegral hb hb1 ht]
  change (∫⁻ x, ∫⁻ η, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*stablePoissonTotal (Measure.dirac x+η)))
        ∂poissonRandomMeasureLaw (stableLogIntensity b) ∂stableLogIntensity b) = _
  simp_rw [he]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,stableLogIntensity_laplace_moment hb.le hr ht,
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hb.le (Real.rpow_nonneg ht.le _))
      (Real.Gamma_pos_of_pos (sub_pos.mpr hr)).le)]

lemma gamma_lintegral_rpow_scale {q b c : ℝ} (hq : -1 < q) (hb : 0 < b) (hc : 0 < c) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^q*Real.exp (-c*t^b))) =
      ENNReal.ofReal (c^(-(q+1)/b)*(1/b)*Real.Gamma ((q+1)/b)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_rpow_mul_exp_neg_mul_rpow hq hb hc) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le),
    integral_rpow_mul_exp_neg_mul_rpow hb hq hc]

def stableJumpMomentE (r : ℝ) (η : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (r*x)) ∂η

@[fun_prop] lemma stableJumpMomentE_measurable (r : ℝ) : Measurable (stableJumpMomentE r) :=
  Measure.measurable_lintegral (by fun_prop)

lemma stablePoisson_palm_laplace' {b r t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hr : b < r) (ht : 0 < t) :
    (∫⁻ η, stableJumpMomentE r η*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)*Real.exp (-Real.Gamma (1-b)*t^b)) := by
  have hh := stablePoisson_palm_laplace hb hb1 hr ht
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top] at hh
  exact hh

lemma stablePoisson_palm_mellin_mul {a b r : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) (hr : b < r) :
    (∫⁻ η, stableJumpMomentE r η*ENNReal.ofReal (stablePoissonTotal η^(a-r))
      ∂poissonRandomMeasureLaw (stableLogIntensity b))*ENNReal.ofReal (Real.Gamma (r-a)) =
      ENNReal.ofReal (Real.Gamma (r-b)*Real.Gamma (1-a/b)*
        (Real.Gamma (1-b))^(a/b-1)) := by
  let P := poissonRandomMeasureLaw (stableLogIntensity b)
  let c := Real.Gamma (1-b)
  have hc : 0 < c := Real.Gamma_pos_of_pos (by linarith)
  have hra : 0 < r-a := by linarith
  let K := fun (η : Measure ℝ) (t : ℝ) => stableJumpMomentE r η*
    ENNReal.ofReal (t^(r-a-1)*Real.exp (-t*stablePoissonTotal η))
  have hm : Measurable (Function.uncurry K) := by dsimp [K]; fun_prop
  have hgamma : ∀ᵐ η ∂P,
      stableJumpMomentE r η*ENNReal.ofReal (stablePoissonTotal η^(a-r))*ENNReal.ofReal (Real.Gamma (r-a)) =
        ∫⁻ t : ℝ in Ioi 0, K η t := by
    filter_upwards [stablePoissonTotal_pos hb hb1] with η hη
    dsimp [K]
    rw [lintegral_const_mul _ (by fun_prop),gamma_lintegral_positive_scale hra hη,
      show -(r-a) = a-r by ring,ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _),mul_assoc]
  have hinner (t : ℝ) (ht : 0 < t) : (∫⁻ η, K η t ∂P) =
      ENNReal.ofReal (b*Real.Gamma (r-b))*ENNReal.ofReal (t^(b-a-1)*Real.exp (-c*t^b)) := by
    have hfac (η : Measure ℝ) : K η t = ENNReal.ofReal (t^(r-a-1))*
        (stableJumpMomentE r η*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))) := by
      dsimp [K]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
      ring
    simp_rw [hfac]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,stablePoisson_palm_laplace' hb hb1 hr ht,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← ENNReal.ofReal_mul (mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hr)).le)]
    congr 1
    have hp : t^(r-a-1)*t^(b-r) = t^(b-a-1) := by rw [← Real.rpow_add ht]; congr 1; ring
    calc
      _ = b*Real.Gamma (r-b)*(t^(r-a-1)*t^(b-r))*Real.exp (-c*t^b) := by dsimp [c]; ring
      _ = _ := by rw [hp]; ring
  calc
    _ = ∫⁻ η, stableJumpMomentE r η*ENNReal.ofReal (stablePoissonTotal η^(a-r))*
        ENNReal.ofReal (Real.Gamma (r-a)) ∂P :=
      (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ η, (∫⁻ t : ℝ in Ioi 0, K η t) ∂P := lintegral_congr_ae hgamma
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ η, K η t ∂P := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (b*Real.Gamma (r-b))*ENNReal.ofReal (t^(b-a-1)*Real.exp (-c*t^b)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hinner t ht
    _ = ENNReal.ofReal (b*Real.Gamma (r-b))*
        ENNReal.ofReal (c^(-((b-a-1)+1)/b)*(1/b)*Real.Gamma (((b-a-1)+1)/b)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,gamma_lintegral_rpow_scale (by linarith) hb hc]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hr)).le)]
      congr 1
      rw [show -((b-a-1)+1)/b = a/b-1 by field_simp; ring,
        show ((b-a-1)+1)/b = 1-a/b by field_simp; ring]
      dsimp [c]
      field_simp

lemma stablePoissonTotal_rpow_lintegral_mul {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) :
    (∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a)
      ∂poissonRandomMeasureLaw (stableLogIntensity b))*ENNReal.ofReal (Real.Gamma (1-a)) =
      ENNReal.ofReal (Real.Gamma (1-a/b)*(Real.Gamma (1-b))^(a/b)) := by
  have he := stablePoisson_palm_mellin_mul hb hb1 ha hb1
  have hrew : (fun η => stableJumpMomentE 1 η*ENNReal.ofReal (stablePoissonTotal η^(a-1))) =ᵐ[
      poissonRandomMeasureLaw (stableLogIntensity b)] (fun η => ENNReal.ofReal (stablePoissonTotal η^a)) := by
    filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hη hpos
    have hJ : stableJumpMomentE 1 η = ENNReal.ofReal (stablePoissonTotal η) := by
      simp only [stableJumpMomentE,one_mul,stablePoissonTotal]
      exact (ENNReal.ofReal_toReal hη).symm
    rw [hJ,← ENNReal.ofReal_mul hpos.le]
    congr 1
    calc
      _ = stablePoissonTotal η^((1:ℝ)+(a-1)) := by rw [Real.rpow_add hpos,Real.rpow_one]
      _ = _ := by congr 1; ring
  rw [lintegral_congr_ae hrew] at he
  rw [he]
  congr 1
  have hc : 0 < Real.Gamma (1-b) := Real.Gamma_pos_of_pos (by linarith)
  calc
    _ = Real.Gamma (1-a/b)*((Real.Gamma (1-b))^((1:ℝ)+(a/b-1))) := by
      rw [Real.rpow_add hc,Real.rpow_one]; ring
    _ = _ := by congr 2; ring

lemma stablePoissonTotal_rpow_integral {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) :
    (∫ η, stablePoissonTotal η^a ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      Real.Gamma (1-a/b)*(Real.Gamma (1-b))^(a/b)/Real.Gamma (1-a) := by
  have hga : 0 < Real.Gamma (1-a) := Real.Gamma_pos_of_pos (by linarith)
  have hgab : 0 < Real.Gamma (1-a/b) := Real.Gamma_pos_of_pos (by
    have : a/b < 1 := (div_lt_one hb).mpr ha
    linarith)
  have hi := stablePoissonTotal_rpow_integrable hb hb1 ha
  have hn : ∀ η : Measure ℝ, 0 ≤ stablePoissonTotal η^a := fun η =>
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have he := stablePoissonTotal_rpow_lintegral_mul hb hb1 ha
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)] at he
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal hga.le,ENNReal.toReal_ofReal
      (mul_nonneg hgab.le (Real.rpow_nonneg (Real.Gamma_pos_of_pos (by linarith : 0 < 1-b)).le _))] at her
  exact (eq_div_iff hga.ne').mpr her

end SphericalPerceptronFreeEnergy

end

end OAI

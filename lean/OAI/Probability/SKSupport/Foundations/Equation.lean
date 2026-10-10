import Mathlib
import OAI.Probability.SKSupport.Diffusion.CompactDrift

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def valueRate (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  -(1/2:ℝ)*curvature W γ t x-(1/2:ℝ)*extend γ.val t*(gradient W γ t x)^2

lemma approxRate_eq (γ : OrderParameter) (n : ℕ) (t x : ℝ) :
    finiteRate (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x =
      -(1/2:ℝ)*iteratedDeriv 2 (approxValue γ n t) x-
        (1/2:ℝ)*approxGamma γ n t*(iteratedDeriv 1 (approxValue γ n t) x)^2 := by
  simp only [finiteRate,finiteSource,approxValue,approxGamma,iteratedDeriv_succ,
    iteratedDeriv_zero]
  ring

lemma approxRate_tendsto (W : BrownianSystem Ω) (γ : OrderParameter) (t : Time)
    (ht : ContinuousAt γ.val t) (x : ℝ) :
    Tendsto (fun n => finiteRate (approxCoeff γ n) (approxMesh n)
      (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x) atTop (𝓝 (valueRate W γ t x)) := by
  have h₂ := (approxValue_derivative_uniform_spatial W γ t.property.1 t.property.2 2).tendsto_at x
  have h₁ := (approxValue_derivative_uniform_spatial W γ t.property.1 t.property.2 1).tendsto_at x
  have hc := approxGamma_tendsto γ t ht
  simp only [approxRate_eq]
  have he : extend γ.val t = γ.val t := by simp [extend,t.property]
  unfold valueRate curvature gradient
  rw [he]
  convert (tendsto_const_nhds.mul h₂ (a := -(1/2:ℝ))).sub
      ((tendsto_const_nhds.mul hc (a := (1/2:ℝ))).mul (h₁.pow 2)) using 1
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]

lemma approxRate_bounded_on (γ : OrderParameter) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ t ∈ Icc (0:ℝ) T, ∀ x,
      |finiteRate (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x| ≤ C := by
  obtain ⟨C,hC,hb⟩ := approxValue_uniform_derivative_bounds γ hT0 hT1 1
  let D := γ.val ⟨T,⟨hT0,hT1⟩⟩
  have hD : 0 ≤ D := γ.nonneg _
  refine ⟨C+D,add_nonneg hC hD,fun n t ht x => ?_⟩
  rw [approxRate_eq]
  have ha := hb n t ht x
  have hg : |iteratedDeriv 1 (approxValue γ n t) x| ≤ 1 := by
    rw [iteratedDeriv_one]
    exact norm_deriv_le_of_lipschitz (finiteValue_lipschitz
      (softAbs_lipschitz (show ((n+1:ℕ):ℝ) ≠ 0 by positivity)) _ _ _ _ _)
  have hc := approxGamma_bounds γ n (⟨t,⟨ht.1,ht.2.trans_lt hT1⟩⟩ : Time)
  have hcd : approxGamma γ n t ≤ D := hc.2.trans (γ.monotone ht.2)
  have hsq : |iteratedDeriv 1 (approxValue γ n t) x|^2 ≤ 1 := by
    nlinarith [abs_nonneg (iteratedDeriv 1 (approxValue γ n t) x)]
  have hc0 : 0 ≤ approxGamma γ n t := hc.1
  refine (abs_sub _ _).trans ?_
  simp only [abs_mul,abs_neg,abs_pow,
    abs_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num),abs_of_nonneg hc0]
  change |iteratedDeriv 2 (approxValue γ n t) x| ≤ C at ha
  nlinarith [mul_le_mul_of_nonneg_left hsq hc0]

lemma approxRate_integral_limit (W : BrownianSystem Ω) (γ : OrderParameter)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) (x : ℝ) :
    Tendsto (fun n => ∫ t in a..b, finiteRate (approxCoeff γ n) (approxMesh n)
      (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x) atTop (𝓝 (∫ t in a..b, valueRate W γ t x)) := by
  obtain ⟨C,hC,hbound⟩ := approxRate_bounded_on γ (ha.trans hab) hb
  have hm : ∀ n, AEStronglyMeasurable (fun t => finiteRate (approxCoeff γ n) (approxMesh n)
      (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x) (volume.restrict (Ioc a b)) := by
    intro n
    exact ((measurable_finiteRate (regularDatum_softAbs (by positivity))
      (softAbs_lipschitz (by positivity)) _ _ _ _).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hdom : ∀ n, ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖finiteRate (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x‖ ≤ C := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using hbound n t ⟨ha.trans ht.1.le,ht.2⟩ x
  have hlim : ∀ᵐ t ∂volume.restrict (Ioc a b), Tendsto
      (fun n => finiteRate (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x)
      atTop (𝓝 (valueRate W γ t x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (γ.ae_continuous).filter_mono (ae_mono Measure.restrict_le_self)] with t ht hc
    have hmem : t ∈ Ico (0:ℝ) 1 := ⟨ha.trans ht.1.le,ht.2.trans_lt hb⟩
    exact approxRate_tendsto W γ ⟨t,hmem⟩ (hc hmem) x
  have hint : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_const (c := C)).1
  have hh := tendsto_integral_of_dominated_convergence (fun _ => C) hm hint hdom hlim
  simpa only [intervalIntegral.integral_of_le hab] using hh

theorem value_integral_rate (W : BrownianSystem Ω) (γ : OrderParameter)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) (x : ℝ) :
    (∫ t in a..b, valueRate W γ t x) = value W γ b x-value W γ a x := by
  have hvb := (approxValue_uniform_spatial W γ (ha.trans hab) hb.le).tendsto_at x
  have hva := (approxValue_uniform_spatial W γ ha (hab.trans hb.le)).tendsto_at x
  have he (n : ℕ) : (∫ t in a..b, finiteRate (approxCoeff γ n) (approxMesh n)
      (softAbs ((n+1:ℕ):ℝ)) (n+1) 0 t x) = approxValue γ n b x-approxValue γ n a x := by
    exact finiteValue_integral_rate (regularDatum_softAbs (by positivity))
      (softAbs_lipschitz (by positivity)) _ _ _ _ ha hab (by rw [approxMesh_horizon]; exact hb.le) x
  exact tendsto_nhds_unique (approxRate_integral_limit W γ ha hab hb x)
    ((hvb.sub hva).congr (fun n => (he n).symm))

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma compactGradient_family (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    BoundedSmoothFamily (compactGradient W γ T) := by
  have hb (n : ℕ) : ∃ C : ℝ≥0, ∀ t x, |iteratedDeriv n (compactGradient W γ T t) x| ≤ C := by
    obtain ⟨C,hC,hb⟩ := value_uniform_derivative_bounds W γ hT0 hT1 n
    refine ⟨⟨C,hC⟩,fun t x => ?_⟩
    change |iteratedDeriv n (deriv (value W γ (stripClamp T t))) x| ≤ C
    simpa only [iteratedDeriv_succ'] using hb (stripClamp T t) (stripClamp_mem hT0 t) x
  refine ⟨(compactGradient_continuous W γ hT0 hT1).measurable,fun t => ?_,hb⟩
  refine ⟨?_,fun n => ?_⟩
  · change ContDiff ℝ ∞ (deriv (value W γ (stripClamp T t)))
    exact (contDiff_infty_iff_deriv.mp (value_contDiff W γ (stripClamp_mem hT0 t).1
      ((stripClamp_mem hT0 t).2.trans_lt hT1))).2
  · obtain ⟨C,hC⟩ := hb n
    exact ⟨C,hC t⟩

def compactValueRate (W : BrownianSystem Ω) (γ : OrderParameter) (T t x : ℝ) : ℝ :=
  valueRate W γ (stripClamp T t) x

lemma compactValueRate_family (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    BoundedSmoothFamily (compactValueRate W γ T) := by
  have hu := compactGradient_family W γ hT0 hT1
  have hc : BoundedSmoothFamily (fun t (_x : ℝ) => compactCoeff γ T t) := by
    apply BoundedSmoothFamily.timeConst (C := ⟨γ.val ⟨T,⟨hT0,hT1⟩⟩,γ.nonneg _⟩) (compactCoeff_measurable γ T)
    intro t
    rw [abs_of_nonneg (compactCoeff_bounds γ hT0 hT1 t).1]
    exact (compactCoeff_bounds γ hT0 hT1 t).2
  have hh := (hu.deriv.const_mul (-(1/2:ℝ))).add ((hc.mul (hu.mul hu)).const_mul (-(1/2:ℝ)))
  convert hh using 1
  funext t x
  change -(1/2:ℝ)*deriv (deriv (value W γ (stripClamp T t))) x-
    (1/2:ℝ)*extend γ.val (stripClamp T t)*(deriv (value W γ (stripClamp T t)) x)^2 =
      -(1/2:ℝ)*deriv (deriv (value W γ (stripClamp T t))) x+
      -(1/2:ℝ)*(extend γ.val (stripClamp T t)*
        (deriv (value W γ (stripClamp T t)) x*deriv (value W γ (stripClamp T t)) x))
  ring

lemma compactRate_integral_derivative (W : BrownianSystem Ω) (γ : OrderParameter)
    {T a b : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (m : ℕ) (x : ℝ) :
    (∫ t in a..b, iteratedDeriv m (compactValueRate W γ T t) x) =
      iteratedDeriv m (value W γ b) x-iteratedDeriv m (value W γ a) x := by
  have he : (fun z => ∫ t in a..b, compactValueRate W γ T t z) =
      (fun z => value W γ b z-value W γ a z) := by
    funext z
    rw [← value_integral_rate W γ ha hab (hb.trans_lt hT1) z]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    simp only [compactValueRate,stripClamp_eq ⟨ha.trans ht.1,ht.2.trans hb⟩]
  have hi := (compactValueRate_family W γ hT0 hT1).iteratedDeriv_integral m a b x
  rw [he,iteratedDeriv_fun_sub (n := m)
    ((value_contDiff W γ (ha.trans hab) (hb.trans_lt hT1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt)
    ((value_contDiff W γ ha (hab.trans_lt (hb.trans_lt hT1))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.contDiffAt)] at hi
  exact hi.symm

theorem value_derivative_time_bound (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ∃ C : ℝ≥0, ∀ a ∈ Icc (0:ℝ) T, ∀ b ∈ Icc (0:ℝ) T, ∀ x,
      |iteratedDeriv m (value W γ b) x-iteratedDeriv m (value W γ a) x| ≤ C*|b-a| := by
  obtain ⟨C,hC⟩ := (compactValueRate_family W γ hT0 hT1).bounds m
  have hh (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (x : ℝ) :
      |iteratedDeriv m (value W γ b) x-iteratedDeriv m (value W γ a) x| ≤ C*|b-a| := by
    rw [← compactRate_integral_derivative W γ hT0 hT1 ha hab hb m x]
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => iteratedDeriv m (compactValueRate W γ T t) x)
      (C := (C:ℝ)) (fun t (_ht : t ∈ uIoc a b) => by
        simpa only [Real.norm_eq_abs] using hC t x)
  refine ⟨C,fun a ha b hb x => ?_⟩
  rcases le_total a b with hab | hba
  · exact hh a b ha.1 hab hb.2 x
  · simpa only [abs_sub_comm] using hh b a hb.1 hba ha.2 x

end ZeroTemperatureSK

end
end

end OAI

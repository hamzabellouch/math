import Mathlib
import OAI.Probability.SKSupport.Foundations.Taylor1Bound
import OAI.Probability.SKSupport.Regularity.BoundedSmoothFamily

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma BoundedSmoothFamily.add {F G : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hG : BoundedSmoothFamily G) :
    BoundedSmoothFamily (fun t x => F t x+G t x) := by
  refine ⟨hF.measurable.add hG.measurable,fun t => (hF.regular t).add (hG.regular t),?_⟩
  intro n
  obtain ⟨A,hA⟩ := hF.bounds n
  obtain ⟨B,hB⟩ := hG.bounds n
  refine ⟨A+B,fun t x => ?_⟩
  rw [iteratedDeriv_fun_add (n := n)
    ((hF.regular t).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    ((hG.regular t).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)]
  exact (abs_add_le _ _).trans (add_le_add (hA t x) (hB t x))

lemma BoundedSmoothFamily.const_mul {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (c : ℝ) : BoundedSmoothFamily (fun t x => c*F t x) :=
  (BoundedSmoothFamily.timeConst (C := Real.nnabs c) measurable_const (fun _ => by simp [Real.coe_nnabs])).mul hF

lemma BoundedSmoothFamily.intervalIntegrable {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (x a b : ℝ) : IntervalIntegrable (fun t => F t x) volume a b := by
  obtain ⟨C,hC⟩ := hF.bound
  apply (intervalIntegrable_const (c := (C:ℝ))).mono_fun
    (hF.measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [] with t
  simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,abs_of_nonneg C.coe_nonneg] using hC t x

lemma BoundedSmoothFamily.hasDerivAt_integral {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (a b x : ℝ) :
    HasDerivAt (fun z => ∫ t in a..b, F t z) (∫ t in a..b, _root_.deriv (F t) x) x := by
  obtain ⟨C,hC⟩ := hF.deriv.bound
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => F t z) (F' := fun z t => _root_.deriv (F t) z)
    (bound := fun _ => (C:ℝ)) (s := Set.univ) (Filter.univ_mem)
    (Eventually.of_forall (fun z => (hF.measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable))
    (hF.intervalIntegrable x a b) ((hF.deriv.measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable) ?_
    (intervalIntegrable_const) ?_).2
  · filter_upwards [] with t ht z hz
    exact hC t z
  · filter_upwards [] with t ht z hz
    exact ((hF.regular t).smooth.differentiable (by simp) z).hasDerivAt

lemma BoundedSmoothFamily.iteratedDeriv_integral {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (n : ℕ) (a b x : ℝ) :
    _root_.iteratedDeriv n (fun z => ∫ t in a..b, F t z) x =
      ∫ t in a..b, _root_.iteratedDeriv n (F t) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n hn =>
    have he : _root_.iteratedDeriv n (fun z => ∫ t in a..b, F t z) =
        fun z => ∫ t in a..b, _root_.iteratedDeriv n (F t) z := funext hn
    rw [iteratedDeriv_succ,he]
    simpa only [iteratedDeriv_succ] using ((hF.iteratedDeriv n).hasDerivAt_integral a b x).deriv

end ZeroTemperatureSK.Heat

end
end
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma tendstoUniformlyOn_deriv_family {A : Type*} {S : Set A}
    {f : ℕ → A → ℝ → ℝ} {g : A → ℝ → ℝ}
    (hf : ∀ n, ∀ t ∈ S, ContDiff ℝ 2 (f n t))
    (hg : ∀ t ∈ S, ContDiff ℝ 2 (g t)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ t ∈ S, ∀ x, |deriv (deriv (f n t)) x| ≤ C)
    (hbg : ∀ t ∈ S, ∀ x, |deriv (deriv (g t)) x| ≤ C)
    (hlim : TendstoUniformlyOn (fun n (p : A × ℝ) => f n p.1 p.2)
      (fun p => g p.1 p.2) atTop (S ×ˢ Set.univ)) :
    TendstoUniformlyOn (fun n (p : A × ℝ) => deriv (f n p.1) p.2)
      (fun p => deriv (g p.1) p.2) atTop (S ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  let h : ℝ := ε / (2*C+1)
  have hh : 0 < h := div_pos hε (by positivity)
  filter_upwards [hlim (ε*h/4) (by positivity)] with n hn p hp
  have hA : ∀ x, |(f n p.1-g p.1) x| ≤ ε*h/4 := by
    intro x
    exact le_of_lt (by simpa only [Real.dist_eq,Pi.sub_apply,abs_sub_comm] using hn (p.1,x) ⟨hp.1,mem_univ _⟩)
  have hd (x : ℝ) : deriv (f n p.1-g p.1) x = deriv (f n p.1) x-deriv (g p.1) x :=
    deriv_sub ((hf n p.1 hp.1).differentiable (by norm_num) x)
      ((hg p.1 hp.1).differentiable (by norm_num) x)
  have hdd (x : ℝ) : deriv (deriv (f n p.1-g p.1)) x =
      deriv (deriv (f n p.1)) x-deriv (deriv (g p.1)) x := by
    rw [show deriv (f n p.1-g p.1) = deriv (f n p.1)-deriv (g p.1) from funext hd]
    exact deriv_sub
      (by simpa only [iteratedDeriv_one] using (hf n p.1 hp.1).differentiable_iteratedDeriv 1 (by norm_num) x)
      (by simpa only [iteratedDeriv_one] using (hg p.1 hp.1).differentiable_iteratedDeriv 1 (by norm_num) x)
  have hB : ∀ x, |deriv (deriv (f n p.1-g p.1)) x| ≤ 2*C := by
    intro x
    rw [hdd]
    exact (abs_sub _ _).trans (by linarith [hb n p.1 hp.1 x,hbg p.1 hp.1 x])
  have hi := derivative_interpolation ((hf n p.1 hp.1).sub (hg p.1 hp.1)) hA hB hh p.2
  have hc : h*(2*C) < ε := by
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*C+1)).mpr
    nlinarith
  have he : 2*(ε*h/4)/h = ε/2 := by field_simp; ring
  change |deriv (f n p.1-g p.1) p.2| ≤ 2*(ε*h/4)/h+h*(2*C)/2 at hi
  rw [he,hd] at hi
  rw [Real.dist_eq,abs_sub_comm]
  linarith

lemma continuousOn_deriv_family {A : Type*} [TopologicalSpace A] {S : Set A}
    {f : A → ℝ → ℝ} (hc : ContinuousOn (fun p : A × ℝ => f p.1 p.2) (S ×ˢ Set.univ))
    (hf : ∀ t ∈ S, ContDiff ℝ 2 (f t)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ∈ S, ∀ x, |deriv (deriv (f t)) x| ≤ C) :
    ContinuousOn (fun p : A × ℝ => deriv (f p.1) p.2) (S ×ˢ Set.univ) := by
  let h : ℕ → ℝ := fun n => 1/((n+1:ℕ):ℝ)
  have hh (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hlim : Tendsto h atTop (𝓝 0) := by
    simpa only [h,Nat.cast_add,Nat.cast_one] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0))
  let F : ℕ → A × ℝ → ℝ := fun n p => (f p.1 (p.2+h n)-f p.1 p.2)/h n
  have hcont (n : ℕ) : ContinuousOn (F n) (S ×ˢ Set.univ) := by
    dsimp [F]
    apply ContinuousOn.div_const
    apply ContinuousOn.sub _ hc
    apply hc.comp (continuous_fst.prodMk (continuous_snd.add_const (h n))).continuousOn
    intro p hp
    exact ⟨hp.1,mem_univ _⟩
  have hconv : TendstoUniformlyOn F (fun p => deriv (f p.1) p.2) atTop (S ×ˢ Set.univ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hc0 : Tendsto (fun n => C/2*h n) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlim (a := C/2)
    filter_upwards [hc0.eventually (Metric.ball_mem_nhds 0 hε)] with n hn p hp
    rw [Real.dist_eq,sub_zero,
      abs_of_nonneg (mul_nonneg (div_nonneg hC (by norm_num)) (hh n).le)] at hn
    have ht := taylor1_bound (hf p.1 hp.1) (hb p.1 hp.1) p.2 (h n)
    have hb' : |F n p-deriv (f p.1) p.2| ≤ C/2*h n := by
      dsimp [F]
      have he : (f p.1 (p.2+h n)-f p.1 p.2)/h n-deriv (f p.1) p.2 =
          (f p.1 (p.2+h n)-f p.1 p.2-deriv (f p.1) p.2*h n)/h n := by field_simp [ne_of_gt (hh n)]
      rw [he,abs_div,abs_of_pos (hh n),div_le_iff₀ (hh n)]
      rw [abs_of_pos (hh n)] at ht
      nlinarith
    rw [Real.dist_eq,abs_sub_comm]
    exact hb'.trans_lt hn
  exact hconv.continuousOn (Filter.Eventually.of_forall hcont).frequently

end ZeroTemperatureSK.Heat

end
end

end OAI

import Mathlib
import OAI.Probability.SKSupport.Control.ControlPayoffConvex
import OAI.Probability.SKSupport.Foundations.SmoothingStep
import OAI.Probability.SKSupport.Control.CoefficientApprox

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def approxValue (γ : OrderParameter) (n : ℕ) : ℝ → ℝ → ℝ :=
  finiteValue (approxCoeff γ n) (approxMesh n) (softAbs ((n+1:ℕ):ℝ)) (n+1) 0

def approxError (γ : OrderParameter) (n : ℕ) : ℝ :=
  Real.log 2 / ((n+1:ℕ):ℝ)+(3/2:ℝ)*∫ s in (0:ℝ)..1, |approxGamma γ n s-extend γ.val s|

lemma approxError_limit (γ : OrderParameter) : Tendsto (approxError γ) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => Real.log 2 / ((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [approxMesh,NNReal.coe_inv,NNReal.coe_natCast,mul_zero,div_eq_mul_inv] using
      tendsto_const_nhds.mul approxMesh_limit (a := Real.log 2)
  have hi := tendsto_const_nhds.mul (approxGamma_L1 γ) (a := (3/2:ℝ))
  have h := hh.add hi
  unfold approxError
  convert h using 1
  simp only [mul_zero,add_zero]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma approxValue_error (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |approxValue γ n t x-value W γ t x| ≤ approxError γ n := by
  apply finiteValue_control_error W γ _ _ _ (approxMesh_horizon n)
    (regularDatum_softAbs (by positivity)) (softAbs_lipschitz (by positivity)) _ ht0 ht1 x
  intro z
  have hh := softAbs_bounds (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity) z
  rw [abs_of_nonneg hh.1]
  exact hh.2

lemma approxValue_uniform (W : BrownianSystem Ω) (γ : OrderParameter) :
    TendstoUniformlyOn (fun n (p : ℝ × ℝ) => approxValue γ n p.1 p.2)
      (fun p => value W γ p.1 p.2) atTop (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(approxError_limit γ).eventually (gt_mem_nhds hε)] with n hn p hp
  rw [Real.dist_eq,abs_sub_comm]
  exact (approxValue_error W γ n hp.1.1 hp.1.2 p.2).trans_lt hn

lemma approxValue_uniform_spatial (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TendstoUniformly (fun n => approxValue γ n t) (value W γ t) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(approxError_limit γ).eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq,abs_sub_comm]
  exact (approxValue_error W γ n ht0 ht1 x).trans_lt hn

lemma approxValue_regular (γ : OrderParameter) (n : ℕ) (t : ℝ) :
    RegularDatum (approxValue γ n t) :=
  finiteValue_regular (regularDatum_softAbs (by positivity))
    (softAbs_lipschitz (by positivity)) _ _ _ _ _

lemma approxValue_uniform_derivative_bounds (γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ t ∈ Icc (0:ℝ) T, ∀ x,
      |iteratedDeriv (m+1) (approxValue γ n t) x| ≤ C := by
  let δ := (1-T)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : T+δ ∈ Ico (0:ℝ) 1 := by dsimp [δ]; constructor <;> linarith
  let D := γ.val ⟨T+δ,hB⟩
  obtain ⟨C,hC,hbound⟩ := finiteGradient_uniform_smoothing m D (γ.nonneg _) δ hδ
  refine ⟨C,hC,fun n t ht x => ?_⟩
  have hc : ∀ s ∈ Icc (0:ℝ) (T+δ),
      finiteCoeff (approxCoeff γ n) (approxMesh n) (n+1) 0 s ≤ D := by
    intro s hs
    have hmem : s ∈ Ico (0:ℝ) 1 := ⟨hs.1,hs.2.trans_lt hB.2⟩
    exact (approxGamma_bounds γ n ⟨s,hmem⟩).2.trans (γ.monotone hs.2)
  have hh := hbound _ (regularDatum_softAbs (show ((n+1:ℕ):ℝ) ≠ 0 by positivity))
    (softAbs_lipschitz (by positivity)) (approxCoeff γ n) (approxMesh n) (n+1) 0 T hT0
    (by rw [approxMesh_horizon]; exact hB.2.le) hc m le_rfl t ht x
  simpa only [approxValue,iteratedDeriv_succ'] using hh

theorem value_contDiff (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ContDiff ℝ ∞ (value W γ t) := by
  apply (smooth_limit_of_uniform_derivative_bounds
    (fun n => (approxValue_regular γ n t).smooth) _
    (approxValue_uniform_spatial W γ ht0 ht1.le)).1
  intro m
  obtain ⟨C,hC,hb⟩ := approxValue_uniform_derivative_bounds γ ht0 ht1 (m+1)
  exact ⟨C,hC,fun n x => hb n t ⟨ht0,le_rfl⟩ x⟩

lemma approxValue_derivative_uniform_spatial (W : BrownianSystem Ω) (γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (m : ℕ) :
    TendstoUniformly (fun n => iteratedDeriv m (approxValue γ n t))
      (iteratedDeriv m (value W γ t)) atTop := by
  apply (smooth_limit_of_uniform_derivative_bounds
    (fun n => (approxValue_regular γ n t).smooth) _
    (approxValue_uniform_spatial W γ ht0 ht1.le)).2 m
  intro j
  obtain ⟨C,hC,hb⟩ := approxValue_uniform_derivative_bounds γ ht0 ht1 (j+1)
  exact ⟨C,hC,fun n x => hb n t ⟨ht0,le_rfl⟩ x⟩

theorem value_uniform_derivative_bounds (W : BrownianSystem Ω) (γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ x,
      |iteratedDeriv (m+1) (value W γ t) x| ≤ C := by
  obtain ⟨C,hC,hb⟩ := approxValue_uniform_derivative_bounds γ hT0 hT1 m
  refine ⟨C,hC,fun t ht x => ?_⟩
  exact iteratedDeriv_limit_bound (m+1)
    (approxValue_derivative_uniform_spatial W γ ht.1 (ht.2.trans_lt hT1) (m+1))
    (fun n x => hb n t ht x) x

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat

lemma cascade_even {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (he : Function.Even f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    Function.Even (cascade c h f N i) := by
  induction N generalizing i with
  | zero => exact he
  | succ N ih =>
    exact logSemigroup_even (cascade_regular hf hLip c h N (i+1)).smooth.continuous.measurable
      (ih (i+1)) (c i) h

lemma finiteValue_even {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (he : Function.Even f) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (t : ℝ) :
    Function.Even (finiteValue c h f N i t) := by
  induction N generalizing i t with
  | zero => exact he
  | succ N ih =>
    by_cases ht : t ≤ h
    · rw [finiteValue_head f c h N i ht]
      have hm := (cascade_regular hf hLip c h N (i+1)).smooth.continuous.measurable
      have heq : backward (c i) h (cascade c h f N (i+1)) t =
          logSemigroup (c i) (Real.toNNReal (h-t)) (cascade c h f N (i+1)) :=
        funext (varianceLogHeat_eq_logSemigroup_toNNReal hm (c i) (h-t))
      rw [heq]
      exact logSemigroup_even hm (cascade_even hf hLip he c h N (i+1)) _ _
    · rw [finiteValue_tail f c h N i (lt_of_not_ge ht)]
      exact ih (i+1) (t-h)

variable {Ω : Type*} [MeasurableSpace Ω]

theorem value_even (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Function.Even (value W γ t) := by
  intro x
  have h₁ := (approxValue_uniform_spatial W γ ht0 ht1).tendsto_at (-x)
  have h₂ := (approxValue_uniform_spatial W γ ht0 ht1).tendsto_at x
  apply tendsto_nhds_unique h₁
  exact h₂.congr (fun n => (finiteValue_even (regularDatum_softAbs (by positivity))
    (softAbs_lipschitz (by positivity)) (softAbs_even _) _ _ _ _ t x).symm)

lemma gradient_odd (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : Function.Odd (gradient W γ t) := by
  intro x
  have hf := (value_contDiff W γ ht0 ht1).differentiable (by simp)
  have hcomp := (hf (-x)).hasDerivAt.comp x ((hasDerivAt_id x).neg)
  have he : (fun y => value W γ t (-y)) = value W γ t := funext (value_even W γ ht0 ht1.le)
  change HasDerivAt (fun y => value W γ t (-y)) _ x at hcomp
  rw [he] at hcomp
  have hd := hcomp.deriv
  change deriv (value W γ t) x = deriv (value W γ t) (-x)*(-1) at hd
  unfold gradient
  linarith

lemma gradient_zero (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : gradient W γ t 0 = 0 := by
  have hh := gradient_odd W γ ht0 ht1 0
  simp only [neg_zero] at hh
  linarith

lemma gradient_monotone (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : Monotone (gradient W γ t) := by
  have hc := (value_convex W γ t ht1.le).monotoneOn_deriv
    (fun x _ => (value_contDiff W γ ht0 ht1).differentiable (by simp) x)
  intro x y hxy
  exact hc (mem_univ x) (mem_univ y) hxy

lemma curvature_nonneg (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (x : ℝ) : 0 ≤ curvature W γ t x :=
  (gradient_monotone W γ ht0 ht1).deriv_nonneg

end ZeroTemperatureSK

end
end

end OAI

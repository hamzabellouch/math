import Mathlib
import OAI.Probability.SKSupport.Parabolic.GradientStability
import OAI.Probability.SKSupport.Diffusion.MixedPathStability
import OAI.Probability.SKSupport.Regularity.MixedIdentity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def perturbationGradientErrors (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) : Set ℝ :=
  Set.range (fun p : ℝ × ℝ => |compactGradient W (perturbation γ β n) T p.1 p.2-compactGradient W γ T p.1 p.2|)

def perturbationGradientError (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) : ℝ :=
  sSup (perturbationGradientErrors W γ β T n)

lemma perturbationGradientErrors_bddAbove (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) :
    BddAbove (perturbationGradientErrors W γ β T n) := by
  refine ⟨2,?_⟩
  rintro z ⟨p,rfl⟩
  have hb := compactGradient_bound W (perturbation γ β n) T.property.1 T.property.2 p.1 p.2
  have hg := compactGradient_bound W γ T.property.1 T.property.2 p.1 p.2
  exact (abs_sub _ _).trans (by linarith)

lemma perturbationGradientError_nonneg (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) :
    0 ≤ perturbationGradientError W γ β T n :=
  (abs_nonneg _).trans (le_csSup (perturbationGradientErrors_bddAbove W γ β T n) ⟨((0:ℝ),(0:ℝ)),rfl⟩)

lemma perturbationGradientError_bound (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) (t x : ℝ) :
    |compactGradient W (perturbation γ β n) T t x-compactGradient W γ T t x| ≤ perturbationGradientError W γ β T n :=
  le_csSup (perturbationGradientErrors_bddAbove W γ β T n) ⟨(t,x),rfl⟩

lemma perturbationGradientError_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) :
    Tendsto (perturbationGradientError W γ β T) atTop (𝓝 0) := by
  obtain ⟨L,hL⟩ := compactGradient_stability W γ T
  rw [Metric.tendsto_nhds]
  intro ε hε
  let h : ℝ := ε/(4*((L:ℝ)+1))
  have hh : 0 < h := by dsimp [h];positivity
  have hLe : (L:ℝ)*h < ε/2 := by
    have hl : 0 < (L:ℝ)+1 := by positivity
    have he : (4*((L:ℝ)+1))*h=ε := by dsimp [h];field_simp
    nlinarith [L.coe_nonneg]
  have hlim : Tendsto (fun n => 3*coefficientDistance (perturbation γ β n) γ/h) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div] using (tendsto_const_nhds.mul (perturbation_distance_limit γ β) (a := (3:ℝ))).div_const h
  filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))] with n hn
  have hb : perturbationGradientError W γ β T n ≤ 3*coefficientDistance (perturbation γ β n) γ/h+(L:ℝ)*h := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨p,rfl⟩
    exact hL (perturbation γ β n) h hh p.1 p.2
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (perturbationGradientError_nonneg W γ β T n)]
  linarith

def perturbationPathError (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ) : ℝ :=
  2*(coefficientDistance (perturbation γ β n) γ+γ.val T*(T:ℝ)*perturbationGradientError W γ β T n)*
    Real.exp ((stripDrift W γ T).rate*T)

lemma perturbationPathError_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) :
    Tendsto (perturbationPathError W γ β T) atTop (𝓝 0) := by
  unfold perturbationPathError
  have hh := (perturbation_distance_limit γ β).add
    (tendsto_const_nhds.mul (perturbationGradientError_limit W γ β T) (a := γ.val T*(T:ℝ)))
  simpa only [mul_zero,zero_add,zero_mul] using
    (tendsto_const_nhds.mul hh (a := (2:ℝ))).mul_const (Real.exp ((stripDrift W γ T).rate*T))

lemma perturbationPathError_bound (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time) (n : ℕ)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) (ξ : Ω) :
    |(mixedStripDrift W (perturbation γ β n) γ T).solution W.driver t ξ-diffusion W γ t ξ| ≤
      perturbationPathError W γ β T n :=
  mixedPath_error W (perturbation γ β n) γ T (perturbationGradientError_nonneg W γ β T n)
    (perturbationGradientError_bound W γ β T n) t ht ξ

lemma perturbationPath_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) (ξ : Ω) :
    Tendsto (fun n => (mixedStripDrift W (perturbation γ β n) γ T).solution W.driver t ξ)
      atTop (𝓝 (diffusion W γ t ξ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(perturbationPathError_limit W γ β T).eventually (gt_mem_nhds hε)] with n hn
  exact (perturbationPathError_bound W γ β T n t ht ξ).trans_lt hn

lemma mixedQ_perturbation_limit (W : BrownianSystem Ω) (γ β : OrderParameter) (T : Time)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    Tendsto (fun n => mixedQ W (perturbation γ β n) γ T t) atTop
      (𝓝 (squareMoment W γ (diffusion W γ) t)) := by
  let := W.isProbability
  let f (n : ℕ) (ξ : Ω) := (compactGradient W γ T t
    ((mixedStripDrift W (perturbation γ β n) γ T).solution W.driver (Real.toNNReal t) ξ))^2
  have hc : Continuous (compactGradient W γ T t) :=
    (compactGradient_continuous W γ T.property.1 T.property.2).comp (continuous_const.prodMk continuous_id)
  have hm (n : ℕ) : AEStronglyMeasurable (f n) W.law :=
    ((hc.measurable.comp ((mixedStripDrift W (perturbation γ β n) γ T).solution_measurable W (Real.toNNReal t))).pow_const 2).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ ξ ∂W.law, ‖f n ξ‖ ≤ 1 := by
    filter_upwards [] with ξ
    have hh := compactGradient_bound W γ T.property.1 T.property.2 t
      ((mixedStripDrift W (perturbation γ β n) γ T).solution W.driver (Real.toNNReal t) ξ)
    rw [abs_le] at hh
    dsimp only [f]
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hl : ∀ᵐ ξ ∂W.law, Tendsto (fun n => f n ξ) atTop
      (𝓝 ((gradient W γ t (diffusion W γ (Real.toNNReal t) ξ))^2)) := by
    filter_upwards [] with ξ
    have hh := (hc.tendsto _).comp (perturbationPath_limit W γ β T (Real.toNNReal t)
      (by rw [Real.coe_toNNReal _ ht.1];exact ht.2) ξ)
    simpa only [Function.comp_apply,f,compactGradient,stripClamp_eq ht] using hh.pow 2
  exact tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ)) hm (integrable_const _) hb hl

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

lemma squareMoment_bounds (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ} (ht : t ≤ 1) :
    0 ≤ squareMoment W γ (diffusion W γ) t ∧ |squareMoment W γ (diffusion W γ) t| ≤ 1 := by
  let := W.isProbability
  refine ⟨integral_nonneg (fun ξ => sq_nonneg _),?_⟩
  have hb : ∀ᵐ ξ ∂W.law, ‖(gradient W γ t (diffusion W γ (Real.toNNReal t) ξ))^2‖ ≤ 1 := by
    filter_upwards [] with ξ
    have hh := abs_le.mp (gradient_abs_le_one W γ t (diffusion W γ (Real.toNNReal t) ξ) ht)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hh := norm_integral_le_of_norm_le_const hb
  simpa [squareMoment,Real.norm_eq_abs] using hh

lemma squareMoment_continuousOn (W : BrownianSystem Ω) (γ : OrderParameter) :
    ContinuousOn (squareMoment W γ (diffusion W γ)) (Ico (0:ℝ) 1) := by
  intro t ht
  exact (squareMoment_hasDerivWithinAt W γ ht.1 ht.2).continuousWithinAt.mono Ico_subset_Ici_self

lemma curvatureMoment_continuousOn_unit (W : BrownianSystem Ω) (γ : OrderParameter) :
    ContinuousOn (curvatureMoment W γ) (Ico (0:ℝ) 1) := by
  intro t ht
  let T : ℝ := (t+1)/2
  have hT0 : 0 ≤ T := by dsimp [T];linarith [ht.1,ht.2]
  have hT1 : T < 1 := by dsimp [T];linarith [ht.1,ht.2]
  have htt : t < T := by dsimp [T];linarith [ht.1,ht.2]
  have hc := curvatureMoment_continuousOn W γ hT0 hT1 t ⟨ht.1,htt.le⟩
  apply hc.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htt)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩

lemma squareMoment_hasDerivAt (W : BrownianSystem Ω) (γ : OrderParameter) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (squareMoment W γ (diffusion W γ)) (curvatureMoment W γ t) t :=
  (squareMoment_hasDerivWithinAt W γ ht0.le ht1).hasDerivAt (Ici_mem_nhds ht0)

lemma squareMoment_weighted_integrable (W : BrownianSystem Ω) (γ : OrderParameter) {η : ℝ → ℝ}
    (hη : Integrable η) : IntervalIntegrable (fun t => η t*squareMoment W γ (diffusion W γ) t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply hη.integrableOn.mul_bdd
  · exact (squareMoment_continuousOn W γ).aestronglyMeasurable measurableSet_Ico
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    exact (squareMoment_bounds W γ ht.2.le).2

end ZeroTemperatureSK

end
end

end OAI

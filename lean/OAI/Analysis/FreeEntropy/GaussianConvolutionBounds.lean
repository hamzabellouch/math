import OAI.Analysis.FreeEntropy.GaussianDecay

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem normal_prefactor_bounded {a b : ℝ} (ha : 0<a) :
    ∃ D : ℝ,0 ≤ D ∧ ∀s∈Icc a b, |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D := by
  have hc : ContinuousOn (fun s : ℝ => -(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)) (Icc a b) := by
    apply continuousOn_const.mul
    apply ContinuousOn.log (by fun_prop)
    intro s hs; exact ne_of_gt (by have : 0<s := ha.trans_le hs.1; positivity)
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro s hs
  exact (show |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D by simpa only [Real.norm_eq_abs] using hD s hs).trans (le_max_left _ _)
 theorem normalKernel_shift_bounds {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (_hK : 0 ≤ K)
    (x y : EuclideanSpace ℝ ι) (hy : ‖y‖ ≤ K) :
    Real.exp (-D-(‖x‖^2+K^2)/a)  ≤  normalKernel s (x-y) ∧
    normalKernel s (x-y)  ≤  Real.exp (D+K^2/(2*b))*Real.exp (-‖x‖^2/(4*b)) := by
  have hs0 : 0<s := ha.trans_le hs.1
  have hb : 0<b := hs0.trans_le hs.2
  have hnorm : ‖x-y‖ ≤ ‖x‖+K := (norm_sub_le x y).trans (add_le_add le_rfl hy)
  have hnorm' : ‖x‖ ≤ ‖x-y‖+K := by
    calc _ = ‖(x-y)+y‖ := by rw [sub_add_cancel]
         _  ≤  ‖x-y‖+‖y‖ := norm_add_le _ _
         _  ≤  _ := add_le_add_right hy _
  have hu : ‖x-y‖^2 ≤ 2*(‖x‖^2+K^2) := by
    nlinarith [sq_nonneg (‖x‖-K),pow_le_pow_left₀ (norm_nonneg _) hnorm 2]
  have hl : ‖x‖^2 ≤ 2*(‖x-y‖^2+K^2) := by
    nlinarith [sq_nonneg (‖x-y‖-K),pow_le_pow_left₀ (norm_nonneg _) hnorm' 2]
  have hdivu : ‖x-y‖^2/(2*s) ≤ (‖x‖^2+K^2)/a := by
    calc _  ≤  ‖x-y‖^2/(2*a) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hs.1])
         _  ≤  _ := by apply (div_le_iff₀ (show 0<2*a by positivity)).mpr; field_simp; nlinarith
  have hdivl : ‖x‖^2/(4*b)-K^2/(2*b) ≤ ‖x-y‖^2/(2*s) := by
    calc _  ≤  ‖x-y‖^2/(2*b) := by apply (le_div_iff₀ (show 0<2*b by positivity)).mpr; field_simp; nlinarith
         _  ≤  _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hs.2])
  constructor
  · apply Real.exp_le_exp.mpr
    have := (abs_le.mp hD).1
    linarith
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp hD).2
    simp only [neg_div] at *
    linarith
 theorem smoothedDensity_bounds (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (hK : 0 ≤ K)
    (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (x : EuclideanSpace ℝ ι) :
    Real.exp (-D-(‖x‖^2+K^2)/a)  ≤  smoothedDensity μ s x ∧
    smoothedDensity μ s x  ≤  Real.exp (D+K^2/(2*b))*Real.exp (-‖x‖^2/(4*b)) := by
  have hi := normalKernel_integrable_finite μ (ha.trans_le hs.1) x
  constructor
  · have h := integral_mono_ae (integrable_const (Real.exp (-D-(‖x‖^2+K^2)/a))) hi
      (hμ.mono (fun y hy => (normalKernel_shift_bounds ha hs hD hK x y hy).1))
    simpa only [smoothedDensity,integral_const,probReal_univ,one_smul] using h
  · have h := integral_mono_ae hi (integrable_const (Real.exp (D+K^2/(2*b))*Real.exp (-‖x‖^2/(4*b))))
      (hμ.mono (fun y hy => (normalKernel_shift_bounds ha hs hD hK x y hy).2))
    simpa only [smoothedDensity,integral_const,probReal_univ,one_smul] using h
 theorem smoothedDensity_log_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b) (_hD0 : 0 ≤ D)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (hK : 0 ≤ K)
    (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (x : EuclideanSpace ℝ ι) :
    |Real.log (smoothedDensity μ s x)| ≤ D+(‖x‖^2+K^2)/a := by
  have hs0 := ha.trans_le hs.1
  have hb : 0<b := hs0.trans_le hs.2
  have hp := smoothedDensity_pos μ hs0 x
  obtain ⟨hl,hu⟩ := smoothedDensity_bounds μ ha hs hD hK hμ x
  rw [abs_le]
  constructor
  · have h := Real.log_le_log (Real.exp_pos _) hl
    rw [Real.log_exp] at h
    linarith
  · have hu' : smoothedDensity μ s x  ≤  Real.exp D := by
      unfold smoothedDensity
      have h := integral_mono_ae (normalKernel_integrable_finite μ hs0 x) (integrable_const (Real.exp D))
        (ae_of_all _ (fun y => (normalKernel_le s hs0 (x-y)).trans (Real.exp_le_exp.mpr (le_trans (le_abs_self _) hD))))
      simpa only [smoothedDensity,integral_const,probReal_univ,one_smul] using h
    have h := Real.log_le_log hp hu'
    rw [Real.log_exp] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
 theorem integrable_of_normBound (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : ℝ} (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) {f : EuclideanSpace ℝ ι → ℝ} (hf : Continuous f) : Integrable f μ := by
  apply integrable_of_compact_ae μ (isCompact_closedBall (0 : EuclideanSpace ℝ ι) K) _ hf.aestronglyMeasurable hf.continuousOn
  simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
 theorem smoothedGradient_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedGradient μ s x i| ≤ ((‖x‖+K)/a)*smoothedDensity μ s x := by
  have hs0 := ha.trans_le hs
  have hi : Integrable (fun y => normalGradient s (x-y) i) μ := integrable_of_normBound μ hμ ((normalGradient_continuous s i).comp (continuous_const.sub continuous_id))
  calc
    _  ≤  ∫y,|normalGradient s (x-y) i| ∂μ := by simpa only [smoothedGradient,Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => normalGradient s (x-y) i)
    _  ≤  ∫y,((‖x‖+K)/a)*normalKernel s (x-y) ∂μ := by
      apply integral_mono_ae hi.norm ((normalKernel_integrable_finite μ hs0 x).const_mul _)
      filter_upwards [hμ] with y hy
      unfold normalGradient
      rw [Real.norm_eq_abs,abs_mul,abs_div,abs_neg,abs_of_pos hs0,abs_of_pos (normalKernel_pos _ _)]
      apply mul_le_mul_of_nonneg_right _ (normalKernel_pos _ _).le
      have hn0 : |(x-y) i| ≤ ‖x-y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i
      have hn : |(x-y) i| ≤ ‖x‖+K := hn0.trans ((norm_sub_le x y).trans (add_le_add le_rfl hy))
      exact (div_le_div_of_nonneg_right hn hs0.le).trans (div_le_div_of_nonneg_left (by positivity) ha hs)
    _ = _ := integral_const_mul _ _
end FiniteEntropySeparation

end

end OAI

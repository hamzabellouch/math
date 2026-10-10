import Mathlib

namespace OAI

/-! Smooth parameter dependence of an integral over a fixed compact interval. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

universe u

namespace ClosedSurfaceR4.SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def partialDerivative (F : P × ℝ → E) (z : P × ℝ) : P →L[ℝ] E :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ P ℝ)

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
lemma contDiff_partialDerivative {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (partialDerivative F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
lemma partial_hasFDerivAt {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (p : P) (t : ℝ) :
    HasFDerivAt (fun q => F (q, t)) (partialDerivative F (p, t)) p := by
  have hi : HasFDerivAt (fun q : P => (q, t)) (ContinuousLinearMap.inl ℝ P ℝ) p := by
    simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] using
      ((ContinuousLinearMap.inl ℝ P ℝ).hasFDerivAt (x := p)).add_const (0, t)
  exact (hF.differentiable (by simp) (p, t)).hasFDerivAt.comp p hi

omit [CompleteSpace E] in
/-- Compactness gives the domination required to differentiate under the
integral. No uniform derivative bound is an extra premise. -/
theorem hasFDerivAt_integral {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (a b : ℝ) (p₀ : P) :
    HasFDerivAt (fun p => ∫ t in a..b, F (p, t))
      (∫ t in a..b, partialDerivative F (p₀, t)) p₀ := by
  have hDs := contDiff_partialDerivative hF
  have hK : IsCompact (closedBall p₀ 1 ×ˢ uIcc a b) :=
    (isCompact_closedBall p₀ 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hDs.continuous.continuousOn
  have hcF (p : P) : Continuous (fun t => F (p, t)) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hcD (p : P) : Continuous (fun t => partialDerivative F (p, t)) :=
    hDs.continuous.comp (continuous_const.prodMk continuous_id)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := ball p₀ 1) (bound := fun _ => C) (ball_mem_nhds p₀ zero_lt_one)
  · exact Eventually.of_forall (fun p => (hcF p).aestronglyMeasurable)
  · exact (hcF p₀).intervalIntegrable a b
  · exact (hcD p₀).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro p hp
    exact hC (p, t) ⟨ball_subset_closedBall hp, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun t p _ => partial_hasFDerivAt hF p t)

/-- Induction on derivative order; the target Banach space is allowed to
change to a continuous-linear-map space at each induction step. -/
theorem contDiff_integral_nat (a b : ℝ) (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : P × ℝ → E), ContDiff ℝ ∞ F →
      ContDiff ℝ n (fun p => ∫ t in a..b, F (p, t)) := by
  induction n with
  | zero =>
    intro E _ _ _ F hF
    apply contDiff_zero.mpr
    exact (show Differentiable ℝ (fun p => ∫ t in a..b, F (p, t)) from
      fun p => (hasFDerivAt_integral hF a b p).differentiableAt).continuous
  | succ n ih =>
    intro E _ _ _ F hF
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨fun p => ∫ t in a..b, partialDerivative F (p, t),
      ih (P →L[ℝ] E) (partialDerivative F) (contDiff_partialDerivative hF),
      fun p => hasFDerivAt_integral hF a b p⟩

/-- Integrating a smooth family on a fixed compact interval preserves all
orders of smoothness. -/
theorem contDiff_integral {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, F (p, t)) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_integral_nat a b n E F hF

end ClosedSurfaceR4.SmoothParameterIntegral

end

end OAI

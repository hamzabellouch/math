import OAI.Geometry.PeriodicTiling.ScalarAverage
import Mathlib.Analysis.Fourier.AddCircle

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Filter MeasureTheory Set
open scoped Topology

private instance unitPeriodPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev UnitAddCircle := AddCircle (1 : ℝ)

def CircleFourierCancellation (u : ℕ → UnitAddCircle) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    Tendsto (complexAverage (fun n => fourier k (u n))) atTop (𝓝 0)

private theorem circle_continuous_integrable (f : C(UnitAddCircle, ℂ)) :
    Integrable f AddCircle.haarAddCircle :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private theorem circle_integral_fourier (k : ℤ) :
    (∫ x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle) =
      if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst k
    simp only [fourier_zero, integral_const, probReal_univ, one_smul]
  · exact integral_eq_zero_of_add_right_eq_neg
      (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hk (show (0 : ℝ) < 1 from zero_lt_one))

private theorem circle_integral_norm_le (f : C(UnitAddCircle, ℂ)) :
    ‖∫ x, f x ∂AddCircle.haarAddCircle‖ ≤ ‖f‖ := by
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := AddCircle.haarAddCircle)
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x))

private theorem circle_average_norm_le (u : ℕ → UnitAddCircle)
    (f : C(UnitAddCircle, ℂ)) (N : ℕ) :
    ‖complexAverage (fun n => f (u n)) N‖ ≤ ‖f‖ :=
  norm_complexAverage_le _ _ (norm_nonneg f) (fun n => f.norm_coe_le_norm (u n)) N

private def circleAveragingSubmodule (u : ℕ → UnitAddCircle) :
    Submodule ℂ C(UnitAddCircle, ℂ) where
  carrier := {f | Tendsto (complexAverage (fun n => f (u n))) atTop
    (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle))}
  zero_mem' := by
    change Tendsto (complexAverage (fun _ => (0 : ℂ))) atTop
      (𝓝 (∫ _ : UnitAddCircle, (0 : ℂ) ∂AddCircle.haarAddCircle))
    have hz : complexAverage (fun _ => (0 : ℂ)) = fun _ => 0 := by
      funext N
      simp [complexAverage]
    rw [hz, integral_zero]
    exact tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    change Tendsto (complexAverage (fun n => f (u n) + g (u n))) atTop
      (𝓝 (∫ x, f x + g x ∂AddCircle.haarAddCircle))
    have ha : complexAverage (fun n => f (u n) + g (u n)) =
        fun N => complexAverage (fun n => f (u n)) N +
          complexAverage (fun n => g (u n)) N := by
      funext N
      exact complexAverage_add _ _ N
    rw [ha, integral_add (circle_continuous_integrable f) (circle_continuous_integrable g)]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change Tendsto (complexAverage (fun n => c * f (u n))) atTop
      (𝓝 (∫ x, c * f x ∂AddCircle.haarAddCircle))
    have ha : complexAverage (fun n => c * f (u n)) =
        fun N => c * complexAverage (fun n => f (u n)) N := by
      funext N
      exact complexAverage_const_mul _ _ N
    rw [ha, integral_const_mul]
    exact hf.const_mul c

private theorem fourier_mem_circleAveragingSubmodule (u : ℕ → UnitAddCircle)
    (hu : CircleFourierCancellation u) (k : ℤ) :
    fourier k ∈ circleAveragingSubmodule u := by
  change Tendsto _ atTop (𝓝 _)
  rw [circle_integral_fourier]
  by_cases hk : k = 0
  · subst k
    simp only [ite_true, fourier_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    exact (complexAverage_const 1 (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))).symm
  · simpa only [ite_eq_right hk] using hu k hk

theorem circle_averages_tendsto_integral (u : ℕ → UnitAddCircle)
    (hu : CircleFourierCancellation u) (f : C(UnitAddCircle, ℂ)) :
    Tendsto (complexAverage (fun n => f (u n))) atTop
      (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle)) := by
  have hspan : Submodule.span ℂ (Set.range (@fourier (1 : ℝ))) ≤
      circleAveragingSubmodule u := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact fourier_mem_circleAveragingSubmodule u hu k
  have hdense : Dense (Submodule.span ℂ (Set.range (@fourier (1 : ℝ))) :
      Set C(UnitAddCircle, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨p, hp, hfp⟩ := hdense.exists_dist_lt f (show 0 < ε / 4 by positivity)
  have hpconv := hspan hp
  change Tendsto (complexAverage (fun n => p (u n))) atTop
    (𝓝 (∫ x, p x ∂AddCircle.haarAddCircle)) at hpconv
  filter_upwards [Metric.tendsto_nhds.mp hpconv (ε / 2) (by positivity)] with N hN
  have havg : ‖complexAverage (fun n => f (u n)) N -
      complexAverage (fun n => p (u n)) N‖ ≤ ‖f - p‖ := by
    rw [← complexAverage_sub]
    exact circle_average_norm_le u (f - p) N
  have hint : ‖(∫ x, p x ∂AddCircle.haarAddCircle) -
      (∫ x, f x ∂AddCircle.haarAddCircle)‖ ≤ ‖f - p‖ := by
    rw [← integral_sub (circle_continuous_integrable p) (circle_continuous_integrable f)]
    simpa only [ContinuousMap.sub_apply, norm_sub_rev] using circle_integral_norm_le (p - f)
  have hbound := norm_add_le
    (complexAverage (fun n => f (u n)) N - complexAverage (fun n => p (u n)) N)
    (complexAverage (fun n => p (u n)) N - (∫ x, f x ∂AddCircle.haarAddCircle))
  have hbound' := norm_add_le
    (complexAverage (fun n => p (u n)) N - (∫ x, p x ∂AddCircle.haarAddCircle))
    ((∫ x, p x ∂AddCircle.haarAddCircle) - (∫ x, f x ∂AddCircle.haarAddCircle))
  simp only [sub_add_sub_cancel] at hbound hbound'
  rw [dist_eq_norm] at hfp hN ⊢
  linarith

theorem denseRange_of_circleFourierCancellation (u : ℕ → UnitAddCircle)
    (hu : CircleFourierCancellation u) : DenseRange u := by
  rw [Metric.denseRange_iff]
  intro x r hr
  by_contra h
  have haway : ∀ n, r ≤ dist x (u n) :=
    fun n => le_of_not_gt (fun hn => h ⟨n, hn⟩)
  let b : C(UnitAddCircle, ℝ) :=
    ⟨fun y => max (r - dist x y) 0,
      (continuous_const.sub (continuous_const.dist continuous_id)).max continuous_const⟩
  have hb0 : ∀ n, b (u n) = 0 := by
    intro n
    exact max_eq_right (sub_nonpos.mpr (haway n))
  have hbx : b x ≠ 0 := by simpa [b, dist_self, max_eq_left hr.le] using hr.ne'
  have hbnonneg : (0 : UnitAddCircle → ℝ) ≤ b := fun y => le_max_right _ _
  have hbint : 0 < ∫ y, b y ∂AddCircle.haarAddCircle :=
    b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace b) hbnonneg hbx
  let bc : C(UnitAddCircle, ℂ) := ⟨fun y => (b y : ℂ), Complex.continuous_ofReal.comp b.continuous⟩
  have hlim := circle_averages_tendsto_integral u hu bc
  have havgzero : complexAverage (fun n => bc (u n)) = fun _ => 0 := by
    funext N
    simp [complexAverage, bc, hb0]
  rw [havgzero] at hlim
  have hi : (∫ y, bc y ∂AddCircle.haarAddCircle) = 0 :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  have hir : (∫ y, b y ∂AddCircle.haarAddCircle) = 0 := by
    apply Complex.ofReal_injective
    change (∫ y, (b y : ℂ) ∂AddCircle.haarAddCircle) = 0 at hi
    rw [integral_complex_ofReal] at hi
    simpa only [Complex.ofReal_zero] using hi
  linarith

end PeriodicTilingThree

end

end OAI

import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace SmoothCurveComposition

noncomputable section

universe u v
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pointwiseLinear (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun h => ⟨fun t => A t (h t), A.continuous.clm_apply h.continuous⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖A‖ (by
      intro h
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg h))).2
      intro t
      exact (A t).le_opNorm (h t) |>.trans
        (mul_le_mul (A.norm_coe_le_norm t) (h.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem pointwiseLinear_apply (A : C(K, E →L[ℝ] F)) (h : C(K, E)) (t : K) :
    pointwiseLinear A h t = A t (h t) := rfl

def pointwiseOperator : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous
    { toFun := fun A : C(K, E →L[ℝ] F) => pointwiseLinear A
      map_add' := by intros; ext h t; simp
      map_smul' := by intros; ext h t; simp }
    1 (by
      intro A
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
      intro h
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg h))).2
      intro t
      exact (A t).le_opNorm (h t) |>.trans
        (mul_le_mul (A.norm_coe_le_norm t) (h.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem pointwiseOperator_apply (A : C(K, E →L[ℝ] F)) :
    pointwiseOperator A = pointwiseLinear A := rfl

variable [FiniteDimensional ℝ E]

theorem hasFDerivAt_postcomp {f : E → F} (hf : ContDiff ℝ 1 f) (u : C(K, E)) :
    HasFDerivAt (ContinuousMap.comp ⟨f, hf.continuous⟩)
      (pointwiseLinear (ContinuousMap.comp ⟨fderiv ℝ f,
        hf.continuous_fderiv (by norm_num)⟩ u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have huc := (isCompact_closedBall (0 : E) (‖u‖ + 1)).uniformContinuousOn_of_continuous
    (hf.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro h hh
  have hhn : ‖h‖ < min δ 1 := by simpa using hh
  have hhδ : ‖h‖ < δ := lt_of_lt_of_le hhn (min_le_left _ _)
  have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hhn (min_le_right _ _)
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2
  intro t
  have hut : u t ∈ Metric.closedBall (0 : E) (‖u‖ + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [u.norm_coe_le_norm t]
  have huht : u t + h t ∈ Metric.closedBall (0 : E) (‖u‖ + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖u t + h t‖ ≤ ‖u t‖ + ‖h t‖ := norm_add_le _ _
      _ ≤ ‖u‖ + ‖h‖ := add_le_add (u.norm_coe_le_norm t) (h.norm_coe_le_norm t)
      _ ≤ ‖u‖ + 1 := by linarith
  have hd : ∀ z ∈ segment ℝ (u t) (u t + h t),
      HasFDerivWithinAt (fun z => f z - (fderiv ℝ f (u t)) z)
        (fderiv ℝ f z - fderiv ℝ f (u t)) (segment ℝ (u t) (u t + h t)) z := by
    intro z hz
    exact ((hf.differentiable (by norm_num) z).hasFDerivAt.sub
      (fderiv ℝ f (u t)).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ segment ℝ (u t) (u t + h t),
      ‖fderiv ℝ f z - fderiv ℝ f (u t)‖ ≤ ε := by
    intro z hz
    have hzb := (convex_closedBall (0 : E) (‖u‖ + 1)).segment_subset hut huht hz
    have hzd : dist z (u t) < δ := by
      rw [dist_eq_norm]
      calc
        ‖z - u t‖ ≤ ‖u t + h t - u t‖ := norm_sub_le_of_mem_segment hz
        _ = ‖h t‖ := by simp
        _ ≤ ‖h‖ := h.norm_coe_le_norm t
        _ < δ := hhδ
    simpa only [dist_eq_norm] using (hδf z hzb (u t) hut hzd).le
  have hm := (convex_segment (u t) (u t + h t)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hb (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have heq : (f (u t + h t) - (fderiv ℝ f (u t)) (u t + h t)) -
      (f (u t) - (fderiv ℝ f (u t)) (u t)) =
      f (u t + h t) - f (u t) - (fderiv ℝ f (u t)) (h t) := by
    rw [map_add]; abel
  rw [heq, add_sub_cancel_left] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm t) hε.le)

theorem contDiff_postcomp_nat (n : ℕ) {f : E → F} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (ContinuousMap.comp (α := K) ⟨f, hf.continuous⟩) := by
  induction n generalizing F with
  | zero =>
      exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp _)
  | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one] at hf ⊢
      refine contDiff_succ_iff_hasFDerivAt.mpr ⟨fun u =>
        pointwiseOperator (ContinuousMap.comp ⟨fderiv ℝ f,
          hf.continuous_fderiv (by positivity)⟩ u), ?_, ?_⟩
      · exact pointwiseOperator.contDiff.comp
          (ih ((contDiff_succ_iff_fderiv.mp hf).2.2))
      · intro u
        exact hasFDerivAt_postcomp (hf.of_le (by exact le_add_of_nonneg_left (by positivity))) u

theorem contDiff_postcomp {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ContinuousMap.comp (α := K) ⟨f, hf.continuous⟩) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_postcomp_nat n ((contDiff_infty.mp hf) n)

end

end SmoothCurveComposition

end

end WeakMTWGlobalSupport

end OAI

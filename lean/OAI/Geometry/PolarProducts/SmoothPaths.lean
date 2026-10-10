import OAI.Geometry.PolarProducts.Contraction

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal

open Set Filter Metric
open scoped Topology ContDiff

namespace SmoothPaths

universe u v

variable {X : Type v} {E F : Type u} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

def applyField (A : C(X, E →L[ℝ] F)) : C(X, E) →L[ℝ] C(X, F) := by
  let L : C(X, E) →ₗ[ℝ] C(X, F) :=
    { toFun := fun u => ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply L.mkContinuous ‖A‖
  intro u
  apply (ContinuousMap.norm_le (L u) (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact ((A t).le_opNorm (u t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))

@[simp] theorem applyField_apply (A : C(X, E →L[ℝ] F)) (u : C(X, E)) (t : X) :
    applyField A u t = A t (u t) := rfl

def applyFieldCLM : C(X, E →L[ℝ] F) →L[ℝ] C(X, E) →L[ℝ] C(X, F) := by
  let L : C(X, E →L[ℝ] F) →ₗ[ℝ] (C(X, E) →L[ℝ] C(X, F)) :=
    { toFun := fun A => applyField A
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hL : ∀ A : C(X, E →L[ℝ] F), ‖L A‖ ≤ 1 * ‖A‖ := by
    intro A
    rw [one_mul]
    apply (applyField A).opNorm_le_bound (norm_nonneg A)
    intro u
    apply (ContinuousMap.norm_le (applyField A u)
      (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
    intro t
    exact ((A t).le_opNorm (u t)).trans
      (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
        (norm_nonneg _) (norm_nonneg _))
  exact LinearMap.mkContinuous (σ := RingHom.id ℝ)
    (E := C(X, E →L[ℝ] F)) (F := C(X, E) →L[ℝ] C(X, F)) L 1 hL

@[simp] theorem applyFieldCLM_apply (A : C(X, E →L[ℝ] F)) :
    applyFieldCLM A = applyField A := rfl

def superpose {f : E → F} (hf : Continuous f) (u : C(X, E)) : C(X, F) :=
  ⟨fun t => f (u t), hf.comp u.continuous⟩

omit [CompactSpace X] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem superpose_apply {f : E → F} (hf : Continuous f)
    (u : C(X, E)) (t : X) : superpose hf u t = f (u t) := rfl

omit [CompactSpace X] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuous_superpose {f : E → F} (hf : Continuous f) :
    Continuous (superpose (X := X) hf) :=
  ContinuousMap.continuous_postcomp ⟨f, hf⟩

theorem hasFDerivAt_superpose [ProperSpace E] {f : E → F}
    (hf : Differentiable ℝ f) (hf' : Continuous (fderiv ℝ f)) (u : C(X, E)) :
    HasFDerivAt (superpose hf.continuous)
      (applyField (superpose hf' u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have huc : UniformContinuousOn (fderiv ℝ f) (closedBall (0 : E) (‖u‖ + 2)) :=
    (isCompact_closedBall (0 : E) (‖u‖ + 2)).uniformContinuousOn_of_continuous hf'.continuousOn
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(X, E)) (lt_min hδ zero_lt_one)] with h hh
  have hhδ : ‖h‖ < δ := (mem_ball_zero_iff.mp hh).trans_le (min_le_left _ _)
  have hh1 : ‖h‖ < 1 := (mem_ball_zero_iff.mp hh).trans_le (min_le_right _ _)
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro t
  have hu : ‖u t‖ ≤ ‖u‖ := u.norm_coe_le_norm t
  have hsmall : ‖h t‖ < δ := (h.norm_coe_le_norm t).trans_lt hhδ
  have hsmall1 : ‖h t‖ < 1 := (h.norm_coe_le_norm t).trans_lt hh1
  have hut : u t ∈ closedBall (0 : E) (‖u‖ + 2) := by
    rw [mem_closedBall_zero_iff]; linarith
  have hall : ∀ y ∈ ball (u t) (min δ 1),
      ‖fderiv ℝ f y - fderiv ℝ f (u t)‖ ≤ ε := by
    intro y hy
    have hdist : dist y (u t) < δ := hy.trans_le (min_le_left _ _)
    have hdist1 : dist y (u t) < 1 := hy.trans_le (min_le_right _ _)
    have hyball : y ∈ closedBall (0 : E) (‖u‖ + 2) := by
      rw [mem_closedBall_zero_iff]
      have hn := norm_le_norm_sub_add y (u t)
      rw [← dist_eq_norm] at hn
      linarith
    exact le_of_lt (by simpa only [dist_eq_norm] using hbound y hyball (u t) hut hdist)
  have hu0 : u t ∈ ball (u t) (min δ 1) := mem_ball_self (lt_min hδ zero_lt_one)
  have huh : u t + h t ∈ ball (u t) (min δ 1) := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_min hsmall hsmall1
  have he := (convex_ball (u t) (min δ 1)).norm_image_sub_le_of_norm_fderiv_le'
    (fun _ _ => hf _) hall hu0 huh
  simp only [add_sub_cancel_left] at he
  exact he.trans (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm t) hε.le)

theorem contDiff_superpose_nat [ProperSpace E] (n : ℕ) {f : E → F}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (superpose (X := X) hf.continuous) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (continuous_superpose hf.continuous)
  | succ n ih =>
    have hn : (↑(n + 1) : WithTop ℕ∞) ≠ 0 := by simp
    have hd : Differentiable ℝ f := hf.differentiable hn
    have hcd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hc : ContDiff ℝ n (fun u : C(X, E) => applyField (superpose hcd.continuous u)) :=
      by simpa only [Function.comp_def, applyFieldCLM_apply] using
        (applyFieldCLM (X := X) (E := E) (F := F)).contDiff.comp (ih hcd)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨_, hc, hasFDerivAt_superpose hd hcd.continuous⟩

theorem contDiff_superpose [ProperSpace E] {f : E → F}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (superpose (X := X) hf.continuous) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_superpose_nat n (contDiff_infty.mp hf n)

end
end SmoothPaths

end LowerBoundInline

end OAI

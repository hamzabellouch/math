import Mathlib

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {τ : Type*} [Fintype τ]

def projectiveAxis (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) : E :=
  f (WithLp.toLp 2 (0,(1:ℝ)))

lemma projectiveAxis_norm (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) :
    ‖projectiveAxis f‖ = 1 := by
  simp [projectiveAxis]

lemma projectiveAxis_inner (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (v : E) :
    inner ℝ v (projectiveAxis f) = (WithLp.ofLp (f.symm v)).2 := by
  rw [← f.apply_symm_apply v]
  change inner ℝ (f (f.symm v)) (f (WithLp.toLp 2 (0,(1:ℝ)))) = _
  rw [f.inner_map_map]
  simp [WithLp.prod_inner_apply]

def projectiveFrameAt (b : OrthonormalBasis τ ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (j : τ) : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E :=
  f.trans (Submodule.reflection (ℝ ∙ (projectiveAxis f - b j))ᗮ)

lemma projectiveFrameAt_axis (b : OrthonormalBasis τ ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (j : τ) :
    projectiveAxis (projectiveFrameAt b f j) = b j := by
  apply Submodule.reflection_sub
  rw [projectiveAxis_norm,b.norm_eq_one]

def signedProjectiveFrame (b : OrthonormalBasis τ ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (j : τ × Bool) : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E :=
  if j.2 then projectiveFrameAt b f j.1 else
    (projectiveFrameAt b f j.1).trans (LinearIsometryEquiv.neg ℝ)

/-- A concrete finite full covering by positive projective hemispheres;
there is no discarded equator in this pointwise statement. -/
lemma signedProjectiveFrame_cover (b : OrthonormalBasis τ ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) {v : E} (hv : v ≠ 0) :
    ∃ j : τ × Bool, 0 < inner ℝ v (projectiveAxis (signedProjectiveFrame b f j)) := by
  have hex : ∃ j : τ, inner ℝ v (b j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply b.repr.injective
    ext j
    simp only [map_zero,PiLp.zero_apply,OrthonormalBasis.repr_apply_apply]
    simpa only [real_inner_comm] using h j
  obtain ⟨j,hj⟩ := hex
  rcases lt_or_gt_of_ne hj with hn | hp
  · refine ⟨(j,false),?_⟩
    change 0 < inner ℝ v (-projectiveAxis (projectiveFrameAt b f j))
    rw [inner_neg_right,projectiveFrameAt_axis]
    linarith
  · refine ⟨(j,true),?_⟩
    change 0 < inner ℝ v (projectiveAxis (projectiveFrameAt b f j))
    rwa [projectiveFrameAt_axis]

end AffineBernstein

end

end OAI

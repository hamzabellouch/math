import OAI.Geometry.SurfaceImmersion.Geometry.ScalarFlatCriticalValues

namespace OAI

/-! Quadratic control on the rank-zero stratum. In dimensions three to
 two and four to three it makes the critical image Hausdorff-null. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology NNReal ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance flatFirstNormed : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance flatFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance flatSecondNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance flatSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

omit [FiniteDimensional ℝ E] in
lemma flat_first_quadratic_bound {f : E → F} (hf : ContDiff ℝ ∞ f)
    (x y : E) (hfirst : fderiv ℝ f x = 0) {M : ℝ} (hM : 0 ≤ M)
    (hsecond : ∀ z ∈ closedBall x ‖y-x‖, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M) :
    ‖f y-f x‖ ≤ M*‖y-x‖^2 := by
  let d := ‖y-x‖
  have hd : 0 ≤ d := norm_nonneg _
  let B := closedBall x d
  have hx : x ∈ B := mem_closedBall_self hd
  have hy : y ∈ B := by simp only [B,d,mem_closedBall,dist_eq_norm,le_refl]
  have hD := hf.fderiv_right (m := ∞) (by simp)
  have hfirst_bound (z : E) (hz : z ∈ B) : ‖fderiv ℝ f z‖ ≤ M*d := by
    have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hD.differentiable (by simp) w) hsecond hx hz
    rw [hfirst,sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using (mem_closedBall.mp hz)) hM)
  have h := (convex_closedBall x d).norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => hf.differentiable (by simp) w) hfirst_bound hx hy
  calc
    _ ≤ (M*d)*‖y-x‖ := h
    _ = M*‖y-x‖^2 := by dsimp [d]; ring

theorem flat_first_local_holder {f : E → F} (hf : ContDiff ℝ ∞ f) (p : E) :
    ∃ C : ℝ≥0, HolderOnWith C 2 f ({x | fderiv ℝ f x = 0} ∩ ball p (1/4)) := by
  have hD := hf.fderiv_right (m := ∞) (by simp)
  have hc := hD.continuous_fderiv (by simp)
  obtain ⟨M,hM⟩ := (isCompact_closedBall p 1).exists_bound_of_continuousOn hc.continuousOn
  let C : ℝ≥0 := ⟨max M 0,le_max_right _ _⟩
  refine ⟨C,?_⟩
  intro x hx y hy
  have hsub : closedBall y ‖x-y‖ ⊆ closedBall p 1 := by
    intro z hz
    have hzp := dist_triangle z y p
    have hxy := dist_triangle x p y
    have hz' : dist z y ≤ dist x y := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hxp : dist x p < 1/4 := hx.2
    have hyp : dist y p < 1/4 := hy.2
    rw [dist_comm p y] at hxy
    change dist z p ≤ 1
    linarith
  have hbound : ‖f x-f y‖ ≤ (C:ℝ)*‖x-y‖^2 :=
    flat_first_quadratic_bound hf y x hy.1 C.2 (fun z hz =>
      (hM z (hsub hz)).trans (le_max_left _ _))
  change edist (f x) (f y) ≤ (C : ℝ≥0∞)*edist x y ^ (2 : ℝ)
  rw [edist_dist,edist_dist,show (2 : ℝ) = (2 : ℕ) by norm_num,ENNReal.rpow_natCast]
  have he := ENNReal.ofReal_le_ofReal hbound
  rw [ENNReal.ofReal_mul (p := (C:ℝ)) C.2,
    ENNReal.ofReal_pow (norm_nonneg (x-y)) 2,ENNReal.ofReal_coe_nnreal] at he
  simpa only [dist_eq_norm] using he

theorem flat_first_image_dimH {f : E → F} (hf : ContDiff ℝ ∞ f) :
    dimH (f '' {x | fderiv ℝ f x = 0}) ≤ (Module.finrank ℝ E : ℝ≥0∞)/2 := by
  have hholder : dimH (f '' {x | fderiv ℝ f x = 0}) ≤
      dimH {x | fderiv ℝ f x = 0}/(2 : ℝ≥0∞) := by
    apply dimH_image_le_of_locally_holder_on (by norm_num : (0 : ℝ≥0) < 2)
    intro p hp
    obtain ⟨C,hC⟩ := flat_first_local_holder hf p
    exact ⟨C,_,inter_mem_nhdsWithin _ (ball_mem_nhds _ (by norm_num)),hC⟩
  have hdim : dimH {x | fderiv ℝ f x = 0} ≤ (Module.finrank ℝ E : ℝ≥0∞) := by
    exact (dimH_mono (subset_univ _)).trans_eq (Real.dimH_univ_eq_finrank E)
  exact hholder.trans (ENNReal.div_le_div_right hdim _)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

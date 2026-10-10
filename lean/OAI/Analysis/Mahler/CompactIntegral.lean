import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace CompactIntegral

def tube (U : Set (ℂ × ℝ)) : Set ℂ := {z | ∀ t ∈ Icc (0 : ℝ) 1, (z,t) ∈ U}

lemma isOpen_tube {U : Set (ℂ × ℝ)} (hU : IsOpen U) : IsOpen (tube U) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨V,W,hV,hW,hzV,hKW,hVW⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact {z}) isCompact_Icc hU (by
      rintro ⟨x,t⟩ ⟨hx,ht⟩
      rcases mem_singleton_iff.mp hx with rfl
      exact hz t ht)
  apply Filter.mem_of_superset (hV.mem_nhds (hzV (mem_singleton z)))
  intro x hx t ht
  exact hVW ⟨hx,hKW ht⟩

variable {E : Type*} [NormedAddCommGroup E] [normedSpaceRealE : NormedSpace ℝ E]

omit normedSpaceRealE in
lemma local_bound [NormedSpace ℝ E] {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} (hF : ContinuousOn F U) {z : ℂ} (hz : z ∈ tube U) :
    ∃ V ∈ 𝓝 z, V ⊆ tube U ∧ ∃ C : ℝ, ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, ‖F (x,t)‖ ≤ C := by
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp ((isOpen_tube hU).mem_nhds hz)
  have hsub : closedBall z (r/2) ×ˢ Icc (0 : ℝ) 1 ⊆ U := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    exact hrV (mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by linarith))) t ht
  obtain ⟨C,hC⟩ := ((isCompact_closedBall z (r/2)).prod isCompact_Icc).bddAbove_image
    ((hF.mono hsub).norm)
  refine ⟨ball z (r/2),ball_mem_nhds z (by linarith),?_,C,?_⟩
  · intro x hx
    exact hrV (mem_ball.mpr ((mem_ball.mp hx).trans (by linarith)))
  · intro x hx t ht
    exact hC (mem_image_of_mem _ ⟨mem_closedBall.mpr (mem_ball.mp hx).le,ht⟩)

omit normedSpaceRealE in
lemma integrable_slice [NormedSpace ℝ E] {U : Set (ℂ × ℝ)} {F : ℂ × ℝ → E}
    (hF : ContinuousOn F U) {x : ℂ} (hx : x ∈ tube U) :
    IntegrableOn (fun t => F (x,t)) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.integrableOn_Icc
  exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun t ht => hx t ht)

lemma continuousOn_integral {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} (hF : ContinuousOn F U) :
    ContinuousOn (fun x => ∫ t in Icc (0 : ℝ) 1, F (x,t)) (tube U) := by
  intro x hx
  obtain ⟨V,hV,hVU,C,hC⟩ := local_bound hU hF hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := fun _ => C)
  · filter_upwards [hV] with y hy
    exact (integrable_slice hF (hVU hy)).aestronglyMeasurable
  · filter_upwards [hV] with y hy
    exact (ae_restrict_mem measurableSet_Icc).mono (fun t ht => hC y hy t ht)
  · exact integrableOn_const (isCompact_Icc.measure_ne_top)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hF.continuousAt (hU.mem_nhds (hx t ht))).comp
      (f := fun y : ℂ => (y,t)) (continuousAt_id.prodMk continuousAt_const)

variable [completeSpaceE : CompleteSpace E]

omit completeSpaceE in
lemma hasFDerivAt_integral [CompleteSpace E] {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} {G : ℂ × ℝ → ℂ →L[ℝ] E}
    (hF : ContinuousOn F U) (hG : ContinuousOn G U)
    (hd : ∀ p ∈ U, HasFDerivAt (fun x => F (x,p.2)) (G p) p.1)
    {x : ℂ} (hx : x ∈ tube U) :
    HasFDerivAt (fun y => ∫ t in Icc (0 : ℝ) 1, F (y,t))
      (∫ t in Icc (0 : ℝ) 1, G (x,t)) x := by
  obtain ⟨V,hV,hVU,C,hC⟩ := local_bound hU hG hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := V)
    (bound := fun _ => C) hV
  · filter_upwards [hV] with y hy
    exact (integrable_slice hF (hVU hy)).aestronglyMeasurable
  · exact integrable_slice hF hx
  · exact (integrable_slice hG hx).aestronglyMeasurable
  · exact (ae_restrict_mem measurableSet_Icc).mono (fun t ht y hy => hC y hy t ht)
  · exact integrableOn_const (isCompact_Icc.measure_ne_top)
  · exact (ae_restrict_mem measurableSet_Icc).mono (fun t ht y hy => hd (y,t) (hVU hy t ht))

/-- Integration over a fixed compact interval preserves every finite smoothness order.
The domain consists of the parameters whose whole compact fiber is in U. -/
theorem contDiffOn_integral_nat (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} (hF : ContDiffOn ℝ n F U) :
    ContDiffOn ℝ n (fun x => ∫ t in Icc (0 : ℝ) 1, F (x,t)) (tube U) := by
  induction n generalizing E with
  | zero => exact contDiffOn_zero.mpr (continuousOn_integral hU hF.continuousOn)
  | succ n ih =>
    let G : ℂ × ℝ → ℂ →L[ℝ] E := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ ℂ ℝ)
    have hG : ContDiffOn ℝ n G U :=
      (hF.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const
    have hd : ∀ p ∈ U, HasFDerivAt (fun x => F (x,p.2)) (G p) p.1 := by
      intro p hp
      have hf := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
      exact hf.hasFDerivAt.comp p.1 ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1))
    have hI := fun x hx => hasFDerivAt_integral hU hF.continuousOn hG.continuousOn hd (x := x) hx
    rw [show ((n+1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω)+1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_tube hU)]
    refine ⟨fun x hx => (hI x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · exact (ih hG).congr (fun x hx => (hI x hx).fderiv)

/-- Full joint C∞ regularity, with no domination assumption. -/
theorem contDiffOn_integral {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in Icc (0 : ℝ) 1, F (x,t)) (tube U) := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_integral_nat n hU (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))

end CompactIntegral

end OAI

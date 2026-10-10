import Mathlib.Analysis.Calculus.MeanValue
import OAI.Geometry.NodalSets.Charts.AdaptedChartFamilyLemmas

namespace OAI

namespace Yau.Geometry
open Set Filter Metric
open scoped ContDiff Topology NNReal
noncomputable section
variable {T E : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

omit [Nontrivial E] in
lemma frame_inverse_continuous (e : T → E ≃L[ℝ] E)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap)) :
    Continuous (fun t ↦ (e t).symm.toContinuousLinearMap) := by
  have hi : Continuous (fun t ↦ ContinuousLinearMap.inverse (e t).toContinuousLinearMap) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hi : ContinuousAt (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
        (e t).toContinuousLinearMap :=
      (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (e t)).continuousAt
    exact ContinuousAt.comp (x := t) (g := ContinuousLinearMap.inverse)
      (f := fun t ↦ (e t).toContinuousLinearMap) hi he.continuousAt
  simpa only [ContinuousLinearMap.inverse_equiv] using hi

omit [CompleteSpace E] [Nontrivial E] in
lemma approximates_of_derivative_bound (f : E → E) (hf : ContDiff ℝ ∞ f)
    (e : E ≃L[ℝ] E) (r : ℝ) (c : ℝ≥0)
    (hD : ∀ x ∈ Metric.ball (0:E) r, ‖fderiv ℝ f x - e.toContinuousLinearMap‖ ≤ c) :
    ApproximatesLinearOn f e.toContinuousLinearMap (Metric.ball 0 r) c := by
  apply LipschitzOnWith.approximatesLinearOn
  apply (convex_ball (0:E) r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x _
    exact (hf.differentiable (by simp) x).sub e.differentiableAt
  · intro x hx
    rw [((hf.differentiable (by simp) x).hasFDerivAt.sub e.toContinuousLinearMap.hasFDerivAt).fderiv]
    exact hD x hx

theorem compact_common_chart
    {s : Set T} (hs : IsCompact s) (f : T → E → E)
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hD : Continuous (fun z : T × E ↦ fderiv ℝ (f z.1) z.2))
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (h0 : ∀ t, fderiv ℝ (f t) 0 = (e t).toContinuousLinearMap)
    (R : ℝ) (hR : 0 < R) :
    ∃ r > 0, r ≤ R ∧ ∃ d > 0, ∀ t ∈ s, ∃ F : OpenPartialHomeomorph E E,
      (F : E → E) = f t ∧ F.source = Metric.ball 0 r ∧
      Metric.closedBall (f t 0) d ⊆ F.target := by
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuousOn (frame_inverse_continuous e he).continuousOn
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let c : ℝ≥0 := ⟨1 / (2*M), by positivity⟩
  have hcpos : 0 < (c:ℝ) := by change 0 < 1 / (2*M); positivity
  have hMc : M * (c:ℝ) = 1/2 := by change M * (1 / (2*M)) = 1/2; field_simp
  have hsmall (t : T) (ht : t ∈ s) : c < ‖(e t).symm.toContinuousLinearMap‖₊⁻¹ := by
    have hn := (e t).symm.norm_pos
    have hb : ‖(e t).symm.toContinuousLinearMap‖ ≤ M := (hC t ht).trans (le_max_left _ _)
    change (c:ℝ) < ‖(e t).symm.toContinuousLinearMap‖⁻¹
    rw [← one_div]
    apply (lt_div_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_right hb hcpos.le]
  have hcGap (t : T) (ht : t ∈ s) :
      (c:ℝ) ≤ ‖(e t).symm.toContinuousLinearMap‖⁻¹ - (c:ℝ) := by
    have hn := (e t).symm.norm_pos
    have hb : ‖(e t).symm.toContinuousLinearMap‖ ≤ M := (hC t ht).trans (le_max_left _ _)
    have hh : 2*(c:ℝ) ≤ ‖(e t).symm.toContinuousLinearMap‖⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hn).mpr
      nlinarith [mul_le_mul_of_nonneg_right hb hcpos.le]
    linarith
  obtain ⟨r0,hr0,hr0i⟩ := compact_family_common_radius hs
    (fun z : T × E ↦ fderiv ℝ (f z.1) z.2 - (e z.1).toContinuousLinearMap)
    (hD.sub (he.comp continuous_fst)) (isOpen_ball (x := (0 : E →L[ℝ] E)) (ε := (c:ℝ)))
    (fun t _ ↦ by simpa [h0, Metric.mem_ball] using hcpos)
  let r := min r0 R
  have hr : 0 < r := lt_min hr0 hR
  have hri (t : T) (ht : t ∈ s) (x : E) (hx : ‖x‖ < r) :=
    hr0i t ht x (lt_of_lt_of_le hx (min_le_left _ _))
  refine ⟨r,hr,min_le_right _ _,(c:ℝ)*(r/2),mul_pos hcpos (by linarith),?_⟩
  intro t ht
  have happ := approximates_of_derivative_bound (f t) (hf t) (e t) r c (fun x hx ↦ by
    have hh := hri t ht x (by simpa using hx)
    exact le_of_lt (by simpa using hh))
  let F := happ.toOpenPartialHomeomorph (f t) (Metric.ball 0 r) (Or.inr (hsmall t ht)) isOpen_ball
  refine ⟨F,rfl,rfl,?_⟩
  apply Set.Subset.trans (Metric.closedBall_subset_closedBall ?_)
    (happ.closedBall_subset_target (Or.inr (hsmall t ht)) isOpen_ball
      (show 0 ≤ r/2 by linarith) (Metric.closedBall_subset_ball (by linarith)))
  exact mul_le_mul_of_nonneg_right (hcGap t ht) (by linarith)

theorem compact_quadratic_injective_charts {s : Set T} (hs : IsCompact s)
    (y : T → E) (hy : Continuous y)
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → E →L[ℝ] E →L[ℝ] E) (hB : Continuous B) :
    ∃ r > 0, ∃ d > 0, ∀ t ∈ s, ∃ F : OpenPartialHomeomorph E E,
      (F : E → E) = quadraticChartMap (y t) (e t) (B t) ∧
      F.source = Metric.ball 0 r ∧ Metric.closedBall (y t) d ⊆ F.target := by
  have hJ : Continuous (fun z : T × E ↦ fderiv ℝ
      (quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  obtain ⟨r,hr,_,d,hd,hF⟩ := compact_common_chart hs
    (fun t ↦ quadraticChartMap (y t) (e t) (B t))
    (fun t ↦ quadraticChartMap_smooth _ _ _) hJ e he
    (fun t ↦ (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv) 1 zero_lt_one
  exact ⟨r,hr,d,hd,fun t ht ↦ by simpa only [quadraticChartMap_zero] using hF t ht⟩

end
end Yau.Geometry

end OAI

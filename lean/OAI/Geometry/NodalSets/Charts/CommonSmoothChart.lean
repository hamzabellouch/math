import OAI.Geometry.NodalSets.Charts.CommonInjectiveChart

namespace OAI

namespace Yau.Geometry
open Set Metric
open scoped ContDiff
noncomputable section
variable {T E : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

theorem compact_quadratic_smooth_charts {s : Set T} (hs : IsCompact s)
    (y : T → E) (hy : Continuous y)
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → E →L[ℝ] E →L[ℝ] E) (hB : Continuous B)
    {U : Set E} (hU : IsOpen U) (hyU : ∀ t ∈ s, y t ∈ U) :
    ∃ r > 0, ∃ d > 0, ∀ t ∈ s, ∃ F : OpenPartialHomeomorph E E,
      (F : E → E) = quadraticChartMap (y t) (e t) (B t) ∧
      F.source = ball 0 r ∧ closedBall (y t) d ⊆ F.target ∧
      F.target ⊆ U ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
      ContDiff ℝ ∞ (F : E → E) := by
  obtain ⟨R,hR,hRi⟩ := compact_quadratic_chart_domain hs y hy e he B hB hU hyU
  have hJ : Continuous (fun z : T × E ↦ fderiv ℝ
      (quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  obtain ⟨r,hr,hrR,d,hd,hF⟩ := compact_common_chart hs
    (fun t ↦ quadraticChartMap (y t) (e t) (B t))
    (fun t ↦ quadraticChartMap_smooth _ _ _) hJ e he
    (fun t ↦ (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv) R hR
  refine ⟨r,hr,d,hd,?_⟩
  intro t ht
  obtain ⟨F,hFe,hFs,hFt⟩ := hF t ht
  have hFR (x : E) (hx : x ∈ F.source) : ‖x‖ < R := by
    rw [hFs, mem_ball, dist_zero_right] at hx
    exact lt_of_lt_of_le hx hrR
  have hsm : ContDiff ℝ ∞ (F : E → E) := by
    rw [hFe]; exact quadraticChartMap_smooth _ _ _
  refine ⟨F,hFe,hFs,by simpa only [quadraticChartMap_zero] using hFt,?_,?_,hsm⟩
  · intro z hz
    have hi := (hRi t ht (F.symm z) (hFR _ (F.map_target hz))).1
    rw [← hFe, F.right_inv hz] at hi
    exact hi
  · intro z hz
    obtain ⟨J,hJe⟩ := (hRi t ht (F.symm z) (hFR _ (F.map_target hz))).2
    have hD : HasFDerivAt (F : E → E) J.toContinuousLinearMap (F.symm z) := by
      rw [hFe, hJe]
      exact (quadraticChartMap_smooth _ _ _).differentiable (by simp) _ |>.hasFDerivAt
    exact (F.contDiffAt_symm hz hD hsm.contDiffAt).contDiffWithinAt

end
end Yau.Geometry

end OAI

import OAI.Geometry.NodalSets.Charts.CommonInvariantCharts

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff NNReal
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem compact_chart_norm_bound {s : Set T} (hs : IsCompact s)
    (p : T → QuadParam Coord) (hp : Continuous p) (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ t ∈ s, ∀ x ∈ closedBall (0:Coord) R,
      ‖rawQuadratic (p t) x - (p t).1‖ ≤ L*‖x‖ := by
  have hc : Continuous (fun z : T × Coord ↦ fderiv ℝ (rawQuadratic (p z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      ((hp.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨C,hC⟩ := (hs.prod (isCompact_closedBall (0:Coord) R)).exists_bound_of_continuousOn hc.continuousOn
  let L : ℝ≥0 := ⟨max C 1, by positivity⟩
  refine ⟨L,le_max_right _ _,?_⟩
  intro t ht x hx
  have hsm : ContDiff ℝ ∞ (rawQuadratic (p t)) :=
    rawQuadratic_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hl : LipschitzOnWith L (rawQuadratic (p t)) (closedBall 0 R) := by
    apply (convex_closedBall (0:Coord) R).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro z _
      exact hsm.differentiable (by simp) z
    · intro z hz
      exact (hC (t,z) ⟨ht,hz⟩).trans (le_max_left _ _)
  have h := hl.dist_le_mul x hx 0 (by simpa using hR)
  simpa [rawQuadratic,dist_eq_norm] using h

lemma gaussian_chart_norm_bound (c N L a b : ℝ)
    (hc : 0 ≤ c) (hN : 0 ≤ N) (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b ≤ L*a) : (c/L^2)*N*b^2 ≤ c*N*a^2 := by
  have hsq : b^2 ≤ L^2*a^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hb (mul_nonneg hL.le ha)).mpr hab
  have hh : b^2/L^2 ≤ a^2 := (div_le_iff₀ (sq_pos_of_pos hL)).mpr (by nlinarith)
  have he := mul_le_mul_of_nonneg_left hh (mul_nonneg hc hN)
  calc
    (c/L^2)*N*b^2 = (c*N)*(b^2/L^2) := by ring
    _ ≤ c*N*a^2 := he

end
end Yau.Geometry

end OAI

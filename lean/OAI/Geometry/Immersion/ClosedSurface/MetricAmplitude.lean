import OAI.Geometry.Immersion.ClosedSurface.PhaseStock
import OAI.Geometry.Immersion.ClosedSurface.MetricBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]



def metricPhaseAmplitude (g : SmoothMetric M) (p : M)
    (Q : PhaseMean.Tensor →L[ℝ] ℝ) (χ : M → ℝ) (w : ℝ) : M → ℝ :=
  fun q => χ q * (Real.sqrt (Q (coordinateMetric g p (coordinateChart p q))) / w)

lemma metricPhaseAmplitude_tsupport (g : SmoothMetric M) (p : M)
    (Q : PhaseMean.Tensor →L[ℝ] ℝ) (χ : M → ℝ) (w : ℝ) :
    tsupport (metricPhaseAmplitude g p Q χ w) ⊆ tsupport χ := tsupport_mul_subset_left



theorem metricPhaseAmplitude_smooth (g : SmoothMetric M) (p : M)
    (Q : PhaseMean.Tensor →L[ℝ] ℝ) (χ : M → ℝ) (w : ℝ)
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hsource : tsupport χ ⊆ (coordinateChart p).source)
    (hpos : ∀ q ∈ tsupport χ, 0 < Q (coordinateMetric g p (coordinateChart p q))) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (metricPhaseAmplitude g p Q χ w) := by
  apply contMDiff_of_tsupport
  intro q hq
  have hqχ := metricPhaseAmplitude_tsupport g p Q χ w hq
  have hqs := hsource hqχ
  have hqx : coordinateChart p q ∈ coordinateDomain p := by
    rw [← coordinateChart_target]
    exact (coordinateChart p).map_source hqs
  have hc := ((coordinateChart_smoothOn p) q hqs).contMDiffAt
    ((coordinateChart p).open_source.mem_nhds hqs)
  have hm := ((coordinateMetric_smoothOn g p) _ hqx).contDiffAt
    ((coordinateDomain_open p).mem_nhds hqx)
  have hQ := Q.contDiff.contMDiff.contMDiffAt.comp q (hm.contMDiffAt.comp q hc)
  have hs := (Real.contDiffAt_sqrt (ne_of_gt (hpos q hqχ))).contMDiffAt.comp q hQ
  exact (hχ q).mul (hs.div_const w)

lemma metricPhaseAmplitude_hasCompactSupport (g : SmoothMetric M) (p : M)
    (Q : PhaseMean.Tensor →L[ℝ] ℝ) (χ : M → ℝ) (w : ℝ)
    (hχ : HasCompactSupport χ) : HasCompactSupport (metricPhaseAmplitude g p Q χ w) :=
  hχ.of_isClosed_subset (isClosed_tsupport _) (metricPhaseAmplitude_tsupport g p Q χ w)



theorem metricPhaseAmplitude_decomposition (g : SmoothMetric M) (p : M)
    (P : PhaseBasis) (χ : M → ℝ) (w : Fin 3 → ℝ)
    (hw : ∀ j, w j ≠ 0)
    (hpos : ∀ q ∈ tsupport χ, ∀ j, 0 ≤ P.Q j (coordinateMetric g p (coordinateChart p q)))
    (q : M) :
    ∑ j, (metricPhaseAmplitude g p (P.Q j) χ (w j) q)^2 • covectorSquare (w j • P.ξ j) =
      (χ q)^2 • coordinateMetric g p (coordinateChart p q) := by
  by_cases hχ : χ q = 0
  · simp [metricPhaseAmplitude,hχ]
  have hq : q ∈ tsupport χ := subset_tsupport χ hχ
  calc
    _ = ∑ j, ((χ q)^2*(P.Q j (coordinateMetric g p (coordinateChart p q)))) • covectorSquare (P.ξ j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [covectorSquare_smul,smul_smul]
      congr 1
      dsimp [metricPhaseAmplitude]
      rw [mul_pow,div_pow,Real.sq_sqrt (hpos q hq j)]
      field_simp [hw j]
    _ = (χ q)^2 • (∑ j, (P.Q j (coordinateMetric g p (coordinateChart p q))) • covectorSquare (P.ξ j)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
    _ = _ := by rw [P.decomposition]

end ClosedSurfaceR4

end

end OAI

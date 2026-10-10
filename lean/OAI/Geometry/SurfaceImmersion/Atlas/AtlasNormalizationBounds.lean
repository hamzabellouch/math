import OAI.Geometry.SurfaceImmersion.Geometry.SafeRadialNormalization
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds

namespace OAI

/-! A fixed C2 atlas budget for radial normalization. A smooth extension
through zero is used only outside the region contributing to localization. -/
noncomputable section
open Set Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma normalized_localization_eq (i : A.centers) (H : M → Space)
    (hH : ∀ p, (1/2 : ℝ) ≤ ‖H p‖) :
    localize (i : M) (A.weight i) (radialNormalize ∘ H) =
      fun x => (A.chartWeight i x)^2 • safeRadialNormalize (A.vectorChartRead i H x) := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · by_cases hw : A.weight i ((chart (i : M)).symm x) = 0
    · simp [localize,chartWeight,hx,hw]
    · have hp := subset_tsupport (A.weight i) hw
      have ho := A.outer_one i _ hp
      simp only [vectorChartRead,localize,chartWeight,indicator_of_mem hx,ho,one_pow,one_smul,
        Function.comp_apply]
      rw [safeRadialNormalize_eq (hH _)]
  · simp [localize,chartWeight,hx]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma radial_normalization_smooth {H : M → Space}
    (hH : ContMDiff planeModel spaceModel ∞ H) (hb : ∀ p, (1/2 : ℝ) ≤ ‖H p‖) :
    ContMDiff planeModel spaceModel ∞ (radialNormalize ∘ H) := by
  have he : radialNormalize ∘ H = safeRadialNormalize ∘ H := by
    funext p
    exact (safeRadialNormalize_eq (hb p)).symm
  rw [he]
  exact safeRadialNormalize_smooth.contMDiff.comp hH

lemma chartWeight_square_compact (i : A.centers) :
    HasCompactSupport (fun x => (A.chartWeight i x)^2) := by
  have hw : HasCompactSupport (A.chartWeight i) :=
    (A.chartWeightCompact i).isCompact.of_isClosed_subset (isClosed_tsupport _)
      (A.supportedChartWeight i).tsupport_subset
  apply hw.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx hz
  exact hx (by simp [hz])

lemma exists_weighted_bound (m : ℕ) {H : M → Space}
    (hH : ContMDiff planeModel spaceModel ∞ H) :
    ∃ C : ℝ, 0 ≤ C ∧ A.WeightedBound 1 m C H := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hH)
    (localize_compact (i : M) (A.weight_support i) H) m
  exact ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),fun i =>
    (hb i).mono_const (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))⟩

theorem radial_normalization_C2_budget (C : ℝ) (hC : 1 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ H : M → Space,
      ContMDiff planeModel spaceModel ∞ H → (∀ p, (1/2 : ℝ) ≤ ‖H p‖) →
      A.WeightedBound 1 2 C H → A.WeightedBound 1 2 D (radialNormalize ∘ H) := by
  classical
  have hlocal (i : A.centers) : ∃ D : ℝ, 0 ≤ D ∧ ∀ H : M → Space,
      ContMDiff planeModel spaceModel ∞ H → (∀ p, (1/2 : ℝ) ≤ ‖H p‖) →
      A.WeightedBound 1 2 C H → WeightedEstimates.WeightedBound univ 1 2 D
        (localize (i : M) (A.weight i) (radialNormalize ∘ H)) := by
    obtain ⟨R,hR,hr⟩ := A.vectorChartRead_bound (V := Space) i 2
    let E := max 1 (R*C)
    have hE : 1 ≤ E := le_max_left _ _
    obtain ⟨B,hB,hb⟩ := compact_coefficient_bound uniqueDiffOn_univ
      (isCompact_closedBall (0 : Space) E) (subset_univ _)
      safeRadialNormalize_smooth.contDiffOn 2
    obtain ⟨W,hW,hw⟩ := compact_smooth_bound ((A.chartWeight_smooth i).pow 2)
      (A.chartWeight_square_compact i) 2
    refine ⟨4*W*(2*B*E^2),by positivity,?_⟩
    intro H hH hnorm hHC
    have hread : WeightedEstimates.WeightedBound univ 1 2 E (A.vectorChartRead i H) :=
      (hr H 1 C zero_lt_one le_rfl (zero_le_one.trans hC) hH hHC).mono_const (le_max_right _ _)
    have hcomp := hread.comp uniqueDiffOn_univ uniqueDiffOn_univ zero_lt_one hE
      (zero_le_one.trans hB) (A.vectorChartRead_smooth i hH).contDiffOn
      safeRadialNormalize_smooth.contDiffOn (fun _ _ => mem_univ _) (by
        intro j hj x hx
        apply hb j hj (A.vectorChartRead i H x)
        simpa only [mem_closedBall,dist_zero_right] using hread.norm_le (mem_univ x))
    rw [A.normalized_localization_eq i H hnorm]
    convert hw.smul_real uniqueDiffOn_univ zero_le_one hW (by positivity)
      ((A.chartWeight_smooth i).pow 2).contDiffOn
      (safeRadialNormalize_smooth.comp (A.vectorChartRead_smooth i hH)).contDiffOn hcomp using 1 <;> norm_num
  choose D hD hd using hlocal
  refine ⟨∑ i, D i,Finset.sum_nonneg (fun i _ => hD i),?_⟩
  intro H hH hnorm hb i
  exact (hd i H hH hnorm hb).mono_const
    (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Atlas.AtlasNormalProjection
import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorNormalProjection

namespace OAI

/-! The atlas projection is a convex sum of the actual pointwise normal
projections. Local exterior estimates therefore pass to the global field. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def chartProjectedNormal (i : A.centers) (F n : M → Space) (p : M) : Space :=
  spaceCoordinates.symm (realNormalPart
    (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)))
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p))) (spaceCoordinates (n p)))

lemma localizedNormalField_at_source (i : A.centers) (n : M → Space) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    A.localizedNormalField i n (planeCoordinateIsometry (chart (i : M) p)) =
      (A.weight i p)^2 • spaceCoordinates (n p) := by
  simp [localizedNormalField,localize,(chart (i : M)).map_source hp,
    (chart (i : M)).left_inv hp]

lemma restored_localProjectedNormal (i : A.centers) (F n : M → Space) (p : M) :
    restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ A.localProjectedNormal i F n) ∘ planeCoordinateIsometry) p =
        (A.weight i p)^2 • A.chartProjectedNormal i F n p := by
  by_cases hs : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hs,Function.comp_apply]
    by_cases hz : A.weight i p = 0
    · have hx : A.planeWeight i (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
        simp [planeWeight,chartWeight,(chart (i : M)).map_source hs,
          (chart (i : M)).left_inv hs,hz]
      simp [A.localProjectedNormal_zero i F n hx,hz]
    · have hp := subset_tsupport (A.weight i) hz
      rw [A.outer_one i p hp,one_smul,localProjectedNormal,
        A.localizedNormalField_at_source i n hs,(realNormalPart_linear _ _).map_smul,
        map_smul]
      rfl
  · have hz : A.weight i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun hp => hs (A.weight_support i hp))
    simp [restore,hs,hz]

lemma projectedNormalField_eq_sum (F n : M → Space) (p : M) :
    A.projectedNormalField F n p =
      ∑ i : A.centers, (A.weight i p)^2 • A.chartProjectedNormal i F n p := by
  unfold projectedNormalField vectorPlaneRestore
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact A.restored_localProjectedNormal i F n p

lemma projectedNormalField_sub_eq (F n : M → Space) (p : M) :
    A.projectedNormalField F n p - n p =
      ∑ i : A.centers, (A.weight i p)^2 • (A.chartProjectedNormal i F n p - n p) := by
  rw [A.projectedNormalField_eq_sum]
  simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,A.partition,one_smul]

/-- A local exterior error is not multiplied by the number of atlas
patches: the squared weights add to one. -/
theorem projectedNormalField_sub_bound (F n : M → Space) (p : M) {ε : ℝ}
    (hlocal : ∀ i : A.centers, A.weight i p ≠ 0 →
      ‖A.chartProjectedNormal i F n p - n p‖ ≤ ε) :
    ‖A.projectedNormalField F n p - n p‖ ≤ ε := by
  rw [A.projectedNormalField_sub_eq]
  calc
    _ ≤ ∑ i : A.centers, ‖(A.weight i p)^2 • (A.chartProjectedNormal i F n p - n p)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : A.centers, (A.weight i p)^2 * ε := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hz : A.weight i p = 0
      · simp [hz]
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hlocal i hz) (sq_nonneg _)
    _ = ε := by rw [← Finset.sum_mul,A.partition,one_mul]

lemma projectedNormalField_ne_zero (F n : M → Space) (p : M)
    (hn : ‖n p‖ = 1) (hclose : ‖A.projectedNormalField F n p - n p‖ < 1) :
    A.projectedNormalField F n p ≠ 0 := by
  intro hz
  simp [hz,hn] at hclose

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

namespace ClosedSurfaceR4.GeometryPreservation
open RealModes NormalFrame VelocityFrame

/-- Uniform stability of the unnormalized projection on a compact family
of old tangent frames. This is the estimate used before normalizing the
finite-atlas sum. -/
theorem compact_raw_normal_projection {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {A B n : X → Vec} (hA : Continuous A) (hB : Continuous B) (hn : Continuous n)
    (hD : ∀ x, gramDet (A x) (B x) ≠ 0)
    (hunit : ∀ x, n x ⬝ᵥ n x = 1)
    (hAn : ∀ x, A x ⬝ᵥ n x = 0) (hBn : ∀ x, B x ⬝ᵥ n x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ A' B' : Vec,
      ‖A'-A x‖ < δ → ‖B'-B x‖ < δ →
      gramDet A' B' ≠ 0 ∧ ‖realNormalPart A' B' (n x)-n x‖ < ε := by
  let J : X → BoundaryProfile := fun x => ![A x,B x,n x,0,0]
  have hJ : Continuous J := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact hA
    · exact hB
    · exact hn
    · exact continuous_const
    · exact continuous_const
  have he (x : X) : profileNormalPart (J x) = n x :=
    realNormalPart_of_perp _ _ _ (hAn x) (hBn x)
  have hreg : Set.range J ⊆ regularBoundaryProfiles := by
    rintro _ ⟨x,rfl⟩
    refine ⟨hD x,?_⟩
    rw [he]
    intro hz
    have hh := hunit x
    norm_num [hz] at hh
  have hK := isCompact_range hJ
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open isOpen_regularBoundaryProfiles hreg
  have hc : ContinuousOn profileNormalPart (Metric.cthickening r (Set.range J)) :=
    fun H hH => (contDiffAt_profileNormalPart (hsub hH).1).continuousAt.continuousWithinAt
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.cthickening.uniformContinuousOn_of_continuous hc) ε hε
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro x A' B' hA' hB'
  let H : BoundaryProfile := ![A',B',n x,0,0]
  have herr : ‖H-J x‖ < min r d := by
    have hbnd : ‖H-J x‖ ≤ max ‖A'-A x‖ ‖B'-B x‖ := by
      apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))).mpr
      intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
      · simp [H,J]
      · simp [H,J]
      · simp [H,J]
    exact hbnd.trans_lt (max_lt hA' hB')
  have hH : H ∈ Metric.cthickening r (Set.range J) :=
    Metric.thickening_subset_cthickening r (Set.range J)
      (Metric.mem_thickening_iff.mpr ⟨J x,mem_range_self x,by
        simpa only [dist_eq_norm] using herr.trans_le (min_le_left r d)⟩)
  have hJ' : J x ∈ Metric.cthickening r (Set.range J) :=
    Metric.self_subset_cthickening (Set.range J) (mem_range_self x)
  have hh := hclose H hH (J x) hJ' (by
    simpa only [dist_eq_norm] using herr.trans_le (min_le_right r d))
  refine ⟨(hsub hH).1,?_⟩
  change ‖profileNormalPart H-n x‖ < ε
  simpa only [dist_eq_norm,he] using hh

end ClosedSurfaceR4.GeometryPreservation

end

end OAI

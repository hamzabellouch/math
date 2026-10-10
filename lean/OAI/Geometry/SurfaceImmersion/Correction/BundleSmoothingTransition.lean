import OAI.Geometry.SurfaceImmersion.Correction.BundleSmoothingIdentity
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingTransition
import OAI.Geometry.SurfaceImmersion.Geometry.LocalizedBundleBounds

namespace OAI

/-! Chart transitions for the actual bundle smoother. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

def bundleTransition (i j : A.centers) (x : Base) : F →L[ℝ] F :=
  (e j).coordChangeL ℝ (e i) ((chart (i : M)).symm x)

variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

lemma bundleTransition_smooth (i j : A.centers) :
    ContDiffOn ℝ ∞ (A.bundleTransition e i j) (transition (i : M) (j : M)).source := by
  apply ContMDiffOn.contDiffOn
  apply (contMDiffOn_coordChangeL (e j) (e i)).comp
    ((chart_symm_smooth (i : M)).mono (fun _ hx => hx.1))
  intro x hx
  exact ⟨hdomain j hx.2, hdomain i ((chart (i : M)).map_target hx.1)⟩

omit [ContMDiffVectorBundle ∞ F E planeModel] in
lemma bundleLocalize_restore (i j : A.centers) (h : Base → F) :
    A.bundleLocalize e i (A.bundleRestore e j h) =
      fun x => A.pairWeight i j x • A.bundleTransition e i j x
        (h (transition (i : M) (j : M) x)) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · have hbi := hdomain i ((chart (i : M)).map_target hi)
      have hbj := hdomain j hj
      simp only [bundleLocalize, bundleComponent, localize, indicator_of_mem hi,
        bundleRestore, map_smul, pairWeight, bundleTransition]
      rw [(e i).continuousLinearMapAt_apply_of_mem ℝ hbi,
        (e j).symmL_apply (R := ℝ) hbj, ← (e j).coordChangeL_apply (R := ℝ) (e i) ⟨hbj, hbi⟩, smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [bundleLocalize, bundleComponent, localize, indicator_of_mem hi,
        bundleRestore, hz, zero_smul, map_zero, smul_zero, pairWeight]
  · simp only [bundleLocalize, localize, pairWeight, indicator_of_notMem hi, zero_smul]

variable [CompactSpace M]

/-- Fiber transitions preserve each weighted derivative norm without a scale loss. -/
theorem bundle_pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → F) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → WeightedBound Set.univ s m C h →
      WeightedBound Set.univ s m (D * C)
        (A.bundleLocalize e i (A.bundleRestore e j h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_clm_composition_bound
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (A.bundleTransition_smooth e hdomain i j) (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.bundleLocalize_restore e hdomain]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

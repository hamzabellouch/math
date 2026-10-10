import OAI.Geometry.SurfaceImmersion.Atlas.BundleAtlasBounds

namespace OAI

/-! Reading a section with an arbitrary compact chart cutoff is bounded by
its atlas norm. This allows phase patches to use unweighted tensor values. -/
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
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)

def bundleCutoff (i : A.centers) (ψ : M → ℝ) (u : ∀ x, E x) : Base → F :=
  localize (i : M) ψ (A.bundleComponent e i u)

include hdomain
omit [ContMDiffVectorBundle ∞ F E planeModel] in
lemma bundleCutoff_restore (i j : A.centers) (ψ : M → ℝ) (h : Base → F) :
    A.bundleCutoff e i ψ (A.bundleRestore e j h) =
      fun x => localize (i : M) ψ (A.outer j) x • A.bundleTransition e i j x
        (h (transition (i : M) (j : M) x)) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · have hbi := hdomain i ((chart (i : M)).map_target hi)
      have hbj := hdomain j hj
      simp only [bundleCutoff, bundleComponent, localize, indicator_of_mem hi,
        bundleRestore, map_smul, bundleTransition]
      rw [(e i).continuousLinearMapAt_apply_of_mem ℝ hbi,
        (e j).symmL_apply (R := ℝ) hbj,
        ← (e j).coordChangeL_apply (R := ℝ) (e i) ⟨hbj,hbi⟩, smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [bundleCutoff, bundleComponent, localize, indicator_of_mem hi,
        bundleRestore, hz, zero_smul, map_zero, smul_zero]
  · simp only [bundleCutoff, localize, indicator_of_notMem hi, zero_smul]

variable [CompactSpace M]

lemma bundleCutoff_smooth (i : A.centers) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart (i : M)).source) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ContDiff ℝ ∞ (A.bundleCutoff e i ψ u) :=
  localize_smooth_on (i : M) hψ hsupp (A.bundleComponent_smooth_on e hdomain i hu)

/-- Cutoff coordinates lose no derivatives and have constants independent of
both the section and its weighted scale. -/
theorem bundleCutoff_bound (i : A.centers) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart (i : M)).source) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ x, E x) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
        (fun x => TotalSpace.mk' F x (u x)) → A.BundleWeightedBound e s m C u →
      WeightedBound univ s m (D * C) (A.bundleCutoff e i ψ u) := by
  classical
  have hb (j : A.centers) : ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → F) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → WeightedBound univ s m C f →
      WeightedBound univ s m (D * C) (A.bundleCutoff e i ψ (A.bundleRestore e j f)) := by
    let K : Set Base := (chart (i : M)) '' (tsupport ψ ∩ tsupport (A.outer j))
    have hK : IsCompact K :=
      ((isClosed_tsupport ψ).inter (isClosed_tsupport (A.outer j))).isCompact.image_of_continuousOn
        ((chart (i : M)).continuousOn.mono (fun _ hx => hsupp hx.1))
    have hKO : K ⊆ (transition (i : M) (j : M)).source := by
      rintro x ⟨p,⟨hp,hq⟩,rfl⟩
      refine ⟨(chart (i : M)).map_source (hsupp hp),?_⟩
      change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
      rw [(chart (i : M)).left_inv (hsupp hp)]
      exact A.outer_support j hq
    obtain ⟨D,hD,hd⟩ := compact_localized_clm_composition_bound
      (transition (i : M) (j : M)).open_source hK hKO
      (localize_smooth (i : M) hψ hsupp (A.outer_smooth j))
      (localize_tsupport_inter (i : M) hsupp (A.outer j))
      (A.bundleTransition_smooth e hdomain i j) (transition_smooth (i : M) (j : M)) m
    refine ⟨D,hD,?_⟩
    intro f s C hs hs1 hC hf hbf
    rw [A.bundleCutoff_restore e hdomain]
    exact hd f s C hs hs1 hC hf hbf
  choose D hD hd using hb
  refine ⟨∑ j : A.centers, D j, Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro u s C hs hs1 hC hu hbu
  have heq : A.bundleCutoff e i ψ u = fun x => ∑ j : A.centers,
      A.bundleCutoff e i ψ (A.bundleRestore e j (A.bundleLocalize e j u)) x := by
    have hu' : u = (fun p => ∑ j : A.centers,
        A.bundleRestore e j (A.bundleLocalize e j u) p) :=
      (funext (A.bundle_sum_restore_localize e hdomain u)).symm
    funext x
    conv_lhs => rw [hu']
    by_cases hx : x ∈ (chart (i : M)).target <;>
      simp [bundleCutoff, bundleComponent, localize, hx, Finset.smul_sum]
  rw [heq, Finset.sum_mul]
  apply WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (A.bundleCutoff_smooth e hdomain i hψ hsupp
      (A.bundleRestore_smooth e hdomain j (A.bundleLocalize_smooth e hdomain j hu))).contDiffOn
  · intro j _
    exact hd j (A.bundleLocalize e j u) s C hs hs1 hC
      (A.bundleLocalize_smooth e hdomain j hu) (hbu j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Atlas.PrescribedAtlasPatch

namespace OAI

/-! Enlarge one outer cutoff's plateau without changing any partition
weight or coordinate chart. -/
noncomputable section
open Set Filter Function Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem enlarge_outer_plateau (i : A.centers) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chart (i : M)).source)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ B : SmoothingAtlas M, ∃ hcenters : B.centers = A.centers,
      (∀ j p, B.weight (hcenters.symm ▸ j) p = A.weight j p) ∧
      (∀ j p, p ∈ tsupport (B.weight j) → B.outer j =ᶠ[𝓝 p] (fun _ => 1)) ∧
      ∀ p ∈ K, B.outer (hcenters.symm ▸ i) =ᶠ[𝓝 p] (fun _ => 1) := by
  classical
  obtain ⟨W,hW,hKW,hWs⟩ := hK.exists_isOpen_closure_subset
    ((chart (i : M)).open_source.mem_nhdsSet.mpr hKs)
  obtain ⟨O,hO,hKO,hOW⟩ := hK.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hKW)
  obtain ⟨β,hβ,_,hβs,hβone⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := planeModel) (n := (⊤ : ℕ∞)) hW isClosed_closure hOW
  have hβsupport : tsupport β ⊆ (chart (i : M)).source := by
    change closure (support β) ⊆ _
    rw [hβs]
    exact hWs
  have hβgerm : ∀ p ∈ K, β =ᶠ[𝓝 p] (fun _ => 1) := by
    intro p hp
    filter_upwards [hO.mem_nhds (hKO hp)] with y hy
    exact (hβone y).mp (subset_closure hy)
  let outer : A.centers → M → ℝ := fun j =>
    if j = i then fun p => A.outer j p + β p - A.outer j p * β p else A.outer j
  have hsmooth (j : A.centers) : ContMDiff planeModel 𝓘(ℝ) ∞ (outer j) := by
    by_cases hj : j = i
    · have he : outer j = (A.outer j + β) - A.outer j * β := by funext p; simp [outer,hj]
      rw [he]
      exact ((A.outer_smooth j).add hβ).sub ((A.outer_smooth j).mul hβ)
    · simpa only [outer,ite_eq_right hj] using A.outer_smooth j
  have hsupp (j : A.centers) : tsupport (outer j) ⊆ (chart (j : M)).source := by
    by_cases hj : j = i
    · subst j
      apply subset_trans (b := tsupport (A.outer i) ∪ tsupport β) ?_
        (union_subset (A.outer_support i) hβsupport)
      apply closure_minimal _ ((isClosed_tsupport (A.outer i)).union (isClosed_tsupport β))
      · intro p hp
        by_contra hh
        have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport (fun ho => hh (Or.inl ho))
        have hb : β p = 0 := image_eq_zero_of_notMem_tsupport (fun hb => hh (Or.inr hb))
        apply hp
        simp [outer,ho,hb]
    · simpa only [outer,ite_eq_right hj] using A.outer_support j
  have hgerm (j : A.centers) (p : M) (hp : p ∈ tsupport (A.weight j)) :
      outer j =ᶠ[𝓝 p] (fun _ => 1) := by
    filter_upwards [houter j p hp] with x hx
    by_cases hj : j = i
    · subst j; simp [outer,hx]
    · simp [outer,hj,hx]
  let B : SmoothingAtlas M := ⟨A.centers,A.weight,outer,A.weight_smooth,A.weight_support,
    hsmooth,hsupp,fun j p hp => (hgerm j p hp).eq_of_nhds,A.partition⟩
  refine ⟨B,rfl,fun _ _ => rfl,hgerm,?_⟩
  intro p hp
  filter_upwards [hβgerm p hp] with x hx
  change outer i x = 1
  simp [outer,hx]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

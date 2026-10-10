import OAI.Probability.SLE.Geometry.CompactPathNeighborhoods
import OAI.Probability.SLE.Loewner.TraceDomainBoundary

namespace OAI

/-! A finite trace together with a bounded real interval is a compact
locally path-connected barrier outside the surviving Loewner domain. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

def traceBoundaryBarrier (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (R : ℝ) : Set ℂ :=
  (γ '' Icc 0 T) ∪ (Complex.ofReal '' Icc (-R) R)

lemma traceBoundaryBarrier_compact {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (T : ℝ≥0) (R : ℝ) : IsCompact (traceBoundaryBarrier γ T R) :=
  (finiteTrace_isCompact hγ T).union (isCompact_Icc.image Complex.continuous_ofReal)

lemma traceBoundaryBarrier_locallyPathConnected {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (T : ℝ≥0) (R : ℝ) (hR : 0≤R) :
    LocallyPathConnectedSpace (traceBoundaryBarrier γ T R) := by
  have : LocallyPathConnectedSpace (γ '' Icc 0 T) := finiteTrace_locallyPathConnected hγ T
  have : LocallyPathConnectedSpace (Icc (-R) R) :=
    (isQuotientMap_projIcc (a := -R) (b := R) (h := by linarith)).locallyPathConnectedSpace
  let p : Icc (-R) R → Complex.ofReal '' Icc (-R) R := fun x => ⟨x,⟨x,x.2,rfl⟩⟩
  have hp : Continuous p := (Complex.continuous_ofReal.comp continuous_subtype_val).subtype_mk _
  have hs : Surjective p := by
    rintro ⟨_,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have : LocallyPathConnectedSpace (Complex.ofReal '' Icc (-R) R) :=
    (hp.isClosedMap.isQuotientMap hp hs).locallyPathConnectedSpace
  exact compact_union_locallyPathConnected (finiteTrace_isCompact hγ T)
    (isCompact_Icc.image Complex.continuous_ofReal)

lemma traceBoundaryBarrier_disjoint_domain (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (R : ℝ) :
    Disjoint (traceBoundaryBarrier γ T R) (survivingDomain γ T) := by
  apply disjoint_left.mpr
  intro z hz hD
  rcases hz with hz | ⟨x,_,rfl⟩
  · exact hD.1.2 hz
  · have him := hD.1.1
    change 0<(x:ℂ).im at him
    simp at him

lemma frontier_mem_traceBoundaryBarrier {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    {T : ℝ≥0} {R : ℝ} {z : ℂ} (hz : z∈frontier (survivingDomain γ T))
    (hR : ‖z‖≤R) : z∈traceBoundaryBarrier γ T R := by
  rcases frontier_survivingDomain_subset hγ T hz with ht | hr
  · exact Or.inl ht
  · right
    change z.im=0 at hr
    refine ⟨z.re,?_,?_⟩
    · have h := (Complex.abs_re_le_norm z).trans hR
      exact ⟨by linarith [(neg_abs_le z.re)],(le_abs_self z.re).trans h⟩
    · apply Complex.ext <;> simp [hr]

lemma traceBoundaryBarrier_uniform_paths {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (T : ℝ≥0) (R : ℝ) (hR : 0≤R) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x∈traceBoundaryBarrier γ T R, ∀ y∈traceBoundaryBarrier γ T R,
      dist x y<δ → ∃ p : Path x y, (∀ s, p s∈traceBoundaryBarrier γ T R) ∧
        ∀ s, dist (p s) x<ε := by
  have : CompactSpace (traceBoundaryBarrier γ T R) :=
    isCompact_iff_compactSpace.mp (traceBoundaryBarrier_compact hγ T R)
  have : LocallyPathConnectedSpace (traceBoundaryBarrier γ T R) :=
    traceBoundaryBarrier_locallyPathConnected hγ T R hR
  obtain ⟨δ,hδ,hpath⟩ := compact_locallyPathConnected_uniform_path
    (A := traceBoundaryBarrier γ T R) ε hε
  refine ⟨δ,hδ,fun x hx y hy hxy => ?_⟩
  obtain ⟨p,hp⟩ := hpath ⟨x,hx⟩ ⟨y,hy⟩ hxy
  exact ⟨p.map continuous_subtype_val,fun s => (p s).property,hp⟩

end SLEExactGauge

end

end OAI

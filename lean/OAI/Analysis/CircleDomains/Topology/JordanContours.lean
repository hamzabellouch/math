import OAI.Analysis.CircleDomains.Topology.CompactRegularLevelContours
import OAI.Analysis.CircleDomains.Selection.RegularContours
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace OAI

/-!
# Circle contours of compact regular levels

Two classical inputs are separated from the contour construction.

* `CompactOneManifoldClassification` is the compact boundaryless case of
  Milnor, *Topology from the Differentiable Viewpoint* (1965), Appendix
  "Classifying 1-Manifolds", theorem p. 55 (proof pp. 55--57).
  https://www.ux1.eiu.edu/~cidelman/Classes/4855%20and%205220/Supplementary%20Texts/MilnorTopDiffVpt.pdf
* `PlanarSchoenflies` is Moise, *Geometric Topology in Dimensions 2 and 3*,
  Graduate Texts in Mathematics 47 (1977), Theorem 10.4: a continuous
  injection of the unit circle into the plane extends to a homeomorphism
  of the plane. DOI: https://doi.org/10.1007/978-1-4612-9906-6

Both are explicit proposition parameters, not axioms. Neither input asserts
the manuscript's obstacle-isolating disk selection. Smooth local charts,
finite components, their planar embeddings and the contour cover are proved.
-/

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- Published input: the compact connected boundaryless case of Milnor's
classification of smooth one-manifolds. -/
def CompactOneManifoldClassification : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace ℝ M],
    IsManifold (𝓘(ℝ)) ∞ M → CompactSpace M → ConnectedSpace M →
    Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓘(ℝ)⟯ M)

/-- Published input: the planar Schoenflies extension theorem in exactly its
circle-to-plane form. -/
def PlanarSchoenflies : Prop :=
  ∀ γ : Circle → ℂ, Continuous γ → Injective γ →
    ∃ H : ℂ ≃ₜ ℂ, ∀ z : Circle, H (z : ℂ) = γ z

private def componentOpen (M : Type) [TopologicalSpace M] [LocallyConnectedSpace M]
    (c : ConnectedComponents M) : Opens M :=
  ⟨ConnectedComponents.mk ⁻¹' {c}, by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simpa only [connectedComponents_preimage_singleton] using
      (isOpen_connectedComponent (x := x))⟩

private theorem componentOpen_connectedSpace (M : Type) [TopologicalSpace M]
    [LocallyConnectedSpace M] (c : ConnectedComponents M) :
    ConnectedSpace (componentOpen M c) := by
  apply isConnected_iff_connectedSpace.mp
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  simpa only [connectedComponents_preimage_singleton] using
    (isConnected_connectedComponent (x := x))

private theorem componentOpen_compactSpace (M : Type) [TopologicalSpace M]
    [LocallyConnectedSpace M] [CompactSpace M] (c : ConnectedComponents M) :
    CompactSpace (componentOpen M c) := by
  apply isCompact_iff_compactSpace.mp
  apply IsClosed.isCompact
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  change IsClosed (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
  simpa only [connectedComponents_preimage_singleton] using
    (isClosed_connectedComponent (x := x))

/-- A compact regular scalar level is covered by finitely many pairwise
disjoint actual embedded smooth circle parametrizations. Only the circle
classification theorem is assumed; its local manifold hypotheses were proved
in `RegularContours`. -/
theorem finite_smooth_circle_contours_of_regularLevel
    (legacyClassification : CompactOneManifoldClassification) {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t)
    (hc : IsCompact {z | f z = t}) :
    Finite (ConnectedComponents {z // f z = t}) ∧
      ∃ γ : ConnectedComponents {z // f z = t} → Circle → ℂ,
        (∀ c, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ c) ∧ Topology.IsEmbedding (γ c)) ∧
        Pairwise (fun c d => Disjoint (range (γ c)) (range (γ d))) ∧
        (⋃ c, range (γ c)) = {z | f z = t} := by
  classical
  let M := {z // f z = t}
  let : ChartedSpace ℝ M := regularLevelChartedSpace hf ht
  let : IsManifold (𝓘(ℝ)) ∞ M := regularLevel_isManifold hf ht
  let : LocallyConnectedSpace M := regularLevel_locallyConnectedSpace hf ht
  let : CompactSpace M := isCompact_iff_compactSpace.mp hc
  let V := componentOpen M
  have hd (c : ConnectedComponents M) : Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓘(ℝ)⟯ V c) := by
    exact legacyClassification (V c) inferInstance (componentOpen_compactSpace M c)
      (componentOpen_connectedSpace M c)
  let d (c : ConnectedComponents M) := Classical.choice (hd c)
  let γ (c : ConnectedComponents M) (z : Circle) : ℂ := ((d c z).val : ℂ)
  refine ⟨finite_connectedComponents_regularLevel hf ht hc, γ, ?_, ?_, ?_⟩
  · intro c
    constructor
    · exact (regularLevel_subtype_contMDiff hf ht).comp
        (contMDiff_subtype_val.comp (d c).contMDiff)
    · exact Topology.IsEmbedding.subtypeVal.comp
        (Topology.IsEmbedding.subtypeVal.comp (d c).toHomeomorph.isEmbedding)
  · intro c₁ c₂ hne
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have hxy : (d c₁ x).val = (d c₂ y).val := Subtype.ext (hx.trans hy.symm)
    have heq := congrArg ConnectedComponents.mk hxy
    have hx' : ConnectedComponents.mk (d c₁ x).val = c₁ := (d c₁ x).property
    have hy' : ConnectedComponents.mk (d c₂ y).val = c₂ := (d c₂ y).property
    exact hne (hx'.symm.trans (heq.trans hy'))
  · ext z
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, x, rfl⟩
      exact (d c x).val.property
    · intro hz
      let w : M := ⟨z, hz⟩
      let c := ConnectedComponents.mk w
      have hw : w ∈ V c := rfl
      obtain ⟨x, hx⟩ := (d c).surjective ⟨w, hw⟩
      apply Set.mem_iUnion.mpr
      refine ⟨c, x, ?_⟩
      exact congrArg (fun q : V c => (q.val : ℂ)) hx

/-- The bounded filled side of one embedded circle is an actual topological
disk. Compact closure, connectedness and the exact boundary are derived from
the ambient Schoenflies extension. -/
theorem exists_filled_disk_of_circle (hschoenflies : PlanarSchoenflies)
    (γ : Circle → ℂ) (hγ : Continuous γ) (hinj : Injective γ) :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
      frontier U = range γ ∧
      Nonempty ((Metric.closedBall (0 : ℂ) 1) ≃ₜ closure U) := by
  obtain ⟨H, hH⟩ := hschoenflies γ hγ hinj
  let U := H '' Metric.ball (0 : ℂ) 1
  have hcl : closure U = H '' Metric.closedBall (0 : ℂ) 1 := by
    dsimp only [U]
    rw [← H.image_closure, closure_ball _ one_ne_zero]
  have hsphere : H '' Metric.sphere (0 : ℂ) 1 = range γ := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, (hH ⟨z, hz⟩).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.property, hH z⟩
  refine ⟨U, H.isOpenMap _ Metric.isOpen_ball,
    (Metric.isConnected_ball zero_lt_one).image H H.continuous.continuousOn, ?_, ?_, ?_⟩
  · rw [hcl]
    exact (isCompact_closedBall (0 : ℂ) 1).image H.continuous
  · dsimp only [U]
    rw [← H.image_frontier, frontier_ball _ one_ne_zero, hsphere]
  · exact ⟨(H.image _).trans (Homeomorph.setCongr hcl.symm)⟩

/-- Apply the constructed regular cutoff and classify all its level
components. The finite smooth contours avoid the entire obstacle, while the
unfilled superlevel neighborhood isolates exactly the chosen compact piece. -/
theorem exists_finite_contours_isolating_obstacle
    (hsard : SmoothPlanarSard) {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ),
      Finite (ConnectedComponents {z // f z = t}) ∧
      ContDiff ℝ ∞ f ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ V ∧
      closure {z | t < f z} ∩ F = A ∧
      (∀ c, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ c) ∧
        Topology.IsEmbedding (γ c) ∧ Disjoint (range (γ c)) F) ∧
      Pairwise (fun c d => Disjoint (range (γ c)) (range (γ d))) ∧
      (⋃ c, range (γ c)) = {z | f z = t} := by
  obtain ⟨f, t, hf, ht, hopen, hAU, hc, hclV, hclF, hlevel, hregular, hdisj, _⟩ :=
    exists_regular_superlevel_isolating_obstacle hsard hA hAF hFA hV hAV
  obtain ⟨hfinite, γ, hγ, hpair, hcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  refine ⟨f, t, γ, hfinite, hf, ht, hopen, hAU, hc, hclV, hclF, ?_, hpair, hcover⟩
  intro c
  refine ⟨(hγ c).1, (hγ c).2, hdisj.mono_left ?_⟩
  rw [← hcover]
  exact Set.subset_iUnion_of_subset c subset_rfl

end CircleDomainRigidity

end OAI

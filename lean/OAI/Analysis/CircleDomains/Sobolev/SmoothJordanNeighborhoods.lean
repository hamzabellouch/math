import OAI.Analysis.CircleDomains.Topology.JordanExteriors
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

/-!
# Finite smooth Jordan neighborhoods

The contour construction in Section 1 of the Koebe manuscript is derived
from the smooth cutoff and regular level, scalar Sard, compact
one-manifold classification, and planar Schoenflies. Outer selection and containment
give the finite family of Jordan neighborhoods.
-/

open Set Filter Function
open scoped Topology ContDiff Manifold

namespace CircleDomainRigidity

/-- Every point of a regular level borders its strict superlevel set.
Otherwise the point is a local maximum, contradicting regularity. -/
theorem frontier_superlevel_eq_regular_level {f : ℂ → ℝ} {t : ℝ}
    (hf : Continuous f) (ht : IsPlanarRegularValue f t) :
    frontier {z | t < f z} = {z | f z = t} := by
  have hU : IsOpen {z | t < f z} := isOpen_lt continuous_const hf
  apply Set.Subset.antisymm
  · intro z hz
    exact (frontier_lt_subset_eq continuous_const hf hz).symm
  · intro z hz
    change f z = t at hz
    rw [hU.frontier_eq]
    refine ⟨?_, by simp [hz]⟩
    by_contra hnot
    have hlocal : IsLocalMax f z := by
      have hnbd : (closure {w | t < f w})ᶜ ∈ 𝓝 z :=
        isClosed_closure.isOpen_compl.mem_nhds hnot
      filter_upwards [hnbd] with w hw
      have hw' : ¬ t < f w := fun h => hw (subset_closure h)
      simpa only [hz] using le_of_not_gt hw'
    exact ht z hz hlocal.fderiv_eq_zero

/-- A connected unbounded exterior cannot enter the bounded side of a
Jordan curve that it misses. This applies to physical inverse images of
quotient Jordan neighborhoods, even when their boundaries are not smooth. -/
theorem closed_jordanInterior_subset_of_unbounded_connected_compl
    (H : ℂ ≃ₜ ℂ) {V : Set ℂ}
    (hV : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ)
    (hfront : frontier (jordanInterior H) ⊆ V) :
    closure (jordanInterior H) ⊆ V := by
  have hsplit : Vᶜ ⊆ jordanInterior H ∨ Vᶜ ⊆ (closure (jordanInterior H))ᶜ := by
    apply hV.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
    · intro z hz
      by_cases hzin : z ∈ jordanInterior H
      · exact Or.inl hzin
      · right
        intro hzcl
        apply hz
        apply hfront
        rw [(jordanInterior_isOpen H).frontier_eq]
        exact ⟨hzcl, hzin⟩
  rcases hsplit with hin | hout
  · exact (hVunbounded ((isCompact_closure_jordanInterior H).isBounded.subset
      (hin.trans subset_closure))).elim
  · exact compl_subset_compl.mp hout

/-- Actual finite smooth Jordan disks covering a chosen compact part of an
obstacle, with disjoint closures contained in the prescribed physical open
set. Its complement is required connected and unbounded precisely for the
hole-filling containment argument. -/
theorem exists_finite_smooth_jordan_cover
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧ A ⊆ ⋃ i ∈ s, jordanInterior (H i) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F := by
  classical
  obtain ⟨f, t, hf, ht, hU, hAU, hUc, hUV, _, hlevel, hregular, havoid, _⟩ :=
    exists_regular_superlevel_isolating_obstacle hsard hA hAF hFA hV hAV
  obtain ⟨hfinite, γ, hγ, hγdisj, hγcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  let : Finite (ConnectedComponents {z // f z = t}) := hfinite
  choose H hH using fun i => hschoenflies (γ i) (hγ i).2.continuous (hγ i).2.injective
  have hfront (i) : frontier (jordanInterior (H i)) = range (γ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hUd : frontier {z | t < f z} = {z | f z = t} :=
    frontier_superlevel_eq_regular_level hf.continuous hregular
  have hfrontlevel (i) : frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
    rw [hfront, ← hγcover]
    exact subset_iUnion (fun i => range (γ i)) i
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hγdisj hij
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hpair
  let : Finite s := hs.to_subtype
  have hsd' : Pairwise (Disjoint on fun i : s => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hsd i.property j.property (fun h => hij (Subtype.ext h))
  have hcover : frontier {z | t < f z} ⊆ ⋃ i : s, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hUd, ← hγcover] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : z ∈ closure (jordanInterior (H i)) := by
      apply frontier_subset_closure
      simpa only [hfront] using hi
    obtain ⟨j, hj, hij⟩ := hdom i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi'⟩
  have hUcover : {z | t < f z} ⊆ ⋃ i : s, jordanInterior (H i) :=
    open_subset_finite_jordanInteriors_of_frontier_subset (fun i : s => H i) hsd'
      hU (hUc.isBounded.subset subset_closure) hcover
      (fun i => hUd.symm ▸ hfrontlevel i)
  refine ⟨f, t, γ, H, s, hs, ?_, hsd, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcover (hAU hz))
    exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
  · intro i _
    apply closed_jordanInterior_subset_of_unbounded_connected_compl (H i) hVconn hVunbounded
    intro z hz
    apply hUV
    apply frontier_subset_closure
    rw [hUd]
    exact hfrontlevel i hz
  · intro i _
    exact ⟨(hγ i).1, (hγ i).2, hfront i, havoid.mono_left (hfrontlevel i)⟩

end CircleDomainRigidity

end OAI

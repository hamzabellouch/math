import OAI.Analysis.CircleDomains.Modulus.ActualWedgeCost
import OAI.Analysis.CircleDomains.Sobolev.OriginalDomainMetric
import Mathlib.Topology.Compactness.SigmaCompact

namespace OAI

/-!
# Choosing the retained core from finite energy

Compact exhaustion of the actual open domain makes the original wedge
integral arbitrarily small. An intervening open neighborhood puts every
prescribed compact subset strictly inside the selected compact core.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_compact_core_small_tail
    {G K₀ : Set (ℝ × ℝ)} (hG : IsOpen G) (hK₀ : IsCompact K₀) (hK₀G : K₀ ⊆ G)
    {f : (ℝ × ℝ) → ℝ} (hf : IntegrableOn f G) (hf0 : ∀ z, 0 ≤ f z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧
      (∫ z in G \ K, f z) < ε := by
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let C := CompactExhaustion.choice G
  let T : ℕ → Set (ℝ × ℝ) := fun n => Subtype.val '' C n
  have hTc (n : ℕ) : IsCompact (T n) := (C.isCompact n).image continuous_subtype_val
  have hTG (n : ℕ) : T n ⊆ G := by
    rintro z ⟨x, _, rfl⟩
    exact x.property
  have hD : Antitone (fun n => G \ T n) := by
    intro m n hmn z hz
    exact ⟨hz.1, fun hzT => hz.2 (image_mono (C.subset hmn) hzT)⟩
  have hempty : (⋂ n, G \ T n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzG := (mem_iInter.mp hz 0).1
    obtain ⟨n, hn⟩ := C.exists_mem ⟨z, hzG⟩
    exact (mem_iInter.mp hz n).2 ⟨⟨z, hzG⟩, hn, rfl⟩
  have ht : Tendsto (fun n => ∫ z in G \ T n, f z) atTop (𝓝 0) := by
    have ht := tendsto_setIntegral_of_antitone
      (fun n => hG.measurableSet.diff (hTc n).isClosed.measurableSet) hD
      ⟨0, hf.mono_set sdiff_subset⟩
    simpa only [hempty, setIntegral_empty] using ht
  obtain ⟨n, hn⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  have hA : IsCompact (K₀ ∪ T n) := hK₀.union (hTc n)
  obtain ⟨V, hV, hAV, hVG, hVc⟩ := exists_open_between_and_isCompact_closure hA hG
    (union_subset hK₀G (hTG n))
  refine ⟨closure V, hVc, (subset_union_left.trans hAV).trans hV.subset_interior_closure, hVG, ?_⟩
  apply lt_of_le_of_lt _ hn
  apply setIntegral_mono_set (hf.mono_set sdiff_subset) (Eventually.of_forall hf0)
  exact Eventually.of_forall (fun z hz => ⟨hz.1, fun hzT =>
    hz.2 (subset_closure (hAV (Or.inr hzT)))⟩)

theorem integrable_coordinateWedges_of_memLp
    {μ : Measure (ℝ × ℝ)} {n : ℕ} (u : Fin n → (ℝ × ℝ) → ℝ)
    (hu : ∀ i, MemLp (planarGradient (u i)) 2 μ) :
    Integrable (coordinateWedges (natCoordinateFamily u) n) μ := by
  have hi (p : UpperPairs n) :=
    integrable_abs_planarWedge_of_memLp (hu (upperPair p).1) (hu (upperPair p).2)
  have hsum := integrable_finsetSum Finset.univ (fun p _ => hi p)
  exact hsum.congr (Eventually.of_forall fun z => (coordinateWedges_eq_sum_upperPairs u z).symm)

/-- The original L² coordinates supply the small-wedge premise needed
by grid selection, after retaining any prescribed compact subset. -/
theorem exists_compact_core_small_wedges
    {G K₀ : Set (ℝ × ℝ)} (hG : IsOpen G) (hK₀ : IsCompact K₀) (hK₀G : K₀ ⊆ G)
    {n : ℕ} (u : Fin n → (ℝ × ℝ) → ℝ)
    (hu : ∀ i, MemLp (planarGradient (u i)) 2 (volume.restrict G))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧
      (∫ z in G \ K, coordinateWedges (natCoordinateFamily u) n z) < ε := by
  exact exists_compact_core_small_tail hG hK₀ hK₀G
    (integrable_coordinateWedges_of_memLp u hu) (coordinateWedges_nonneg _ _) hε

end CircleDomainRigidity.FiniteTransfer

end

end OAI

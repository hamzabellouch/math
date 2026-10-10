import OAI.Analysis.CircleDomains.Rigidity.MaskedCircleCost
import OAI.Analysis.CircleDomains.Transfer.RegularCore

namespace OAI

/-!
# Regular cores for the masked circle data

The original L² bounds on the separate masks make the actual masked
wedge sum integrable. A regular retained core contains all mask
boundaries and leaves an arbitrarily small tail. The original cutoff
construction then supplies the compactly supported smooth interpolation.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem integrable_maskedCircleWedges_of_memLp
    {μ : Measure (ℝ × ℝ)} {n : ℕ}
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, MemLp (circleGradient (f i)) 2 (μ.restrict (M i))) :
    Integrable (maskedCircleWedges M f) μ := by
  have hi (i : Fin n) : MemLp ((M i).indicator (circleGradient (f i))) 2 μ :=
    (memLp_indicator_iff_restrict (hM i)).mpr (hf i)
  exact integrable_finsetSum univ (fun p _ =>
    integrable_abs_planarWedge_of_memLp (hi (upperPair p).1) (hi (upperPair p).2))

theorem maskedCircleWedges_nonneg
    {n : ℕ} (M : Fin n → Set (ℝ × ℝ))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (z : ℝ × ℝ) :
    0 ≤ maskedCircleWedges M f z :=
  sum_nonneg (fun _ _ => abs_nonneg _)

/-- The core is constructed from the original masked energy. Its
regularity uses only the previously identified scalar Sard input. -/
theorem exists_regular_masked_core_and_cutoff
    (hsard : SmoothPlanarSard) {G K₀ : Set (ℝ × ℝ)}
    (hG : IsOpen G) (hGc : IsCompact Gᶜ) (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ G)
    {n : ℕ} (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (hboundaryG : ∀ i, frontier (M i) ⊆ G)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, MemLp (circleGradient (f i)) 2 ((volume.restrict G).restrict (M i)))
    {η : ℝ} (hη : 0 < η) :
    ∃ (ψ : (ℝ × ℝ) → ℝ) (t : ℝ) (K : Set (ℝ × ℝ)) (χ : (ℝ × ℝ) → ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ t ∈ Set.Ioo 0 1 ∧
      (∀ z, ψ z = t → fderiv ℝ ψ z ≠ 0) ∧ K = {z | ψ z ≤ t} ∧
      IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧ IsCompact (closure Kᶜ) ∧
      (∀ i, frontier (M i) ⊆ interior K) ∧
      (∫ z in G \ K, maskedCircleWedges M f z) < η ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ z, χ z ∈ Set.Icc 0 1) ∧
      (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧ (∀ᶠ z in 𝓝ˢ Gᶜ, χ z = 1) ∧
      MemLp (planarGradient χ) 2 volume := by
  let A := K₀ ∪ ⋃ i, frontier (M i)
  have hA : IsClosed A := hK₀.union (isClosed_iUnion_of_finite fun _ => isClosed_frontier)
  have hAG : A ⊆ G := union_subset hK₀G (iUnion_subset hboundaryG)
  obtain ⟨ψ, t, K, hψ, hψc, ht, hreg, hKeq, hK, hAK, hKG, hKc, htail⟩ :=
    exists_regular_core_small_tail hsard hG hGc hA hAG
      (integrable_maskedCircleWedges_of_memLp M hM f hf) (maskedCircleWedges_nonneg M f) hη
  obtain ⟨χ, hχ, hχc, hχrange, hχzero, hχone, hχ2⟩ :=
    exists_cutoff_near_complement hGc hK hKG
  refine ⟨ψ, t, K, χ, hψ, hψc, ht, hreg, hKeq, hK,
    subset_union_left.trans hAK, hKG, hKc, ?_, htail,
    hχ, hχc, hχrange, hχzero, hχone, hχ2⟩
  intro i
  exact (subset_iUnion_of_subset i (Subset.refl _)).trans (subset_union_right.trans hAK)

end CircleDomainRigidity.FiniteTransfer

end

end OAI

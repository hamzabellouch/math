import OAI.Analysis.Mahler.InteriorStokes

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

/-- Compact regular-sublevel hypotheses yield
boundary patches, cutoffs and volume localization with the
interior term eliminated. This does not identify the terms as boundary flux. -/
theorem exists_regular_sublevel_localization {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    {g : (Fin (n+1) → ℝ) → ℝ} {R : ℝ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hreg : ∀ x ∈ U, g x = R → fderiv ℝ g x ≠ 0)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 1 ω U) :
    ∃ (a : RegularBoundaryAtlas (n+1) U g (frontier (regularSublevel U g R)))
      (W : Set (Fin (n+1) → ℝ))
      (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin (n+1) → ℝ)
        (Fin (n+1) → ℝ) (closure W)),
      IsOpen W ∧ closure (regularSublevel U g R) ⊆ W ∧
      (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ i, tsupport (ρ (some i)) ⊆ (a.patch i).domain) ∧
      (∀ x ∈ W, ∑ i, ρ i x = 1) ∧
      (∫ x in regularSublevel U g R, extDeriv ω x (coordinateBasis (n+1))) =
        ∑ i : a.Index, ∫ x in regularSublevel U g R,
          extDeriv (fun z => ρ (some i) z • ω z) x (coordinateBasis (n+1)) := by
  obtain ⟨a⟩ := exists_sublevelBoundaryAtlas hU hg hc hcl hreg
  obtain ⟨W, ρ, hWo, hCW, _, hρsub, hρc, hsum⟩ :=
    exists_sublevel_partition hU hg.continuousOn hc a
  refine ⟨a, W, ρ, hWo, hCW, hρc, (fun i => hρsub (some i)), hsum, ?_⟩
  have hρU (i : Option a.Index) : tsupport (ρ i) ⊆ U := by
    apply (hρsub i).trans
    cases i with
    | none => exact inter_subset_left
    | some i => exact (a.patch i).domain_U
  exact integral_extDeriv_boundary_patches ρ ω hWo (subset_closure.trans hCW)
    (isOpen_regularSublevel hU hg.continuousOn).measurableSet hsum hρc
    (fun i x hx => hω.contDiffAt (hU.mem_nhds (hρU i hx))) (hρsub none)

end MahlerStokes

end

end OAI

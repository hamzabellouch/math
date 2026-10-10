import OAI.Analysis.BoundedHochschild.RightAveragingOrbit

namespace OAI

/-! A minimal compact convex invariant family of right averages. The proof
uses the finite intersection property and does not presume a fixed point. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Invariance under every finite normalized right average. -/
def RightAverageInvariant (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (K : Set (M → WeakDual ℂ X)) : Prop :=
  ∀ (n : ℕ) (m : Fin n → M), (∑ i, m i * star (m i) = 1) →
    Set.MapsTo (weakRightAverage e m) K K

/-- The averaging orbit contains a minimal nonempty closed convex invariant
subset. The separate module-map step must still show that it is a singleton. -/
theorem exists_minimal_right_averages (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) :
    ∃ K : Set (M → WeakDual ℂ X), K ⊆ weakRightAverageOrbit e T ∧
      K.Nonempty ∧ IsClosed K ∧ Convex ℝ K ∧ RightAverageInvariant e K ∧
      ∀ L : Set (M → WeakDual ℂ X), L ⊆ K → L.Nonempty → IsClosed L →
        Convex ℝ L → RightAverageInvariant e L → K ⊆ L := by
  classical
  let B := weakRightAverageOrbit e T
  have hBc : IsCompact B := weakRightAverageOrbit_isCompact e hno T hT
  let S : Set (Set (M → WeakDual ℂ X)) :=
    {K | K ⊆ B ∧ K.Nonempty ∧ IsClosed K ∧ Convex ℝ K ∧ RightAverageInvariant e K}
  have hBS : B ∈ S := ⟨Set.Subset.rfl, weakRightAverageOrbit_nonempty e T,
    isClosed_closure, weakRightAverageOrbit_convex e T,
    fun _ m hm => weakRightAverageOrbit_invariant e m hm T⟩
  obtain ⟨K, hKB, hK⟩ := zorn_superset_nonempty S (fun c hc hchain hcne => by
    have : Nonempty c := hcne.to_subtype
    have hn : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun L hL J hJ => by
          rcases hchain.total hL hJ with h | h
          · exact ⟨L, hL, Set.Subset.rfl, h⟩
          · exact ⟨J, hJ, h, Set.Subset.rfl⟩)
        (fun L hL => (hc hL).2.1)
        (fun L hL => hBc.of_isClosed_subset (hc hL).2.2.1 (hc hL).1)
        (fun L hL => (hc hL).2.2.1)
    refine ⟨⋂₀ c, ⟨?_, hn, ?_, ?_, ?_⟩, fun L hL => Set.sInter_subset_of_mem hL⟩
    · obtain ⟨L, hL⟩ := hcne
      exact (Set.sInter_subset_of_mem hL).trans (hc hL).1
    · exact isClosed_sInter (fun L hL => (hc hL).2.2.1)
    · intro x hx y hy r s hr hs hrs
      apply Set.mem_sInter.mpr
      intro L hL
      exact (hc hL).2.2.2.1 (Set.mem_sInter.mp hx L hL)
        (Set.mem_sInter.mp hy L hL) hr hs hrs
    · intro n m hm x hx
      apply Set.mem_sInter.mpr
      intro L hL
      exact (hc hL).2.2.2.2 n m hm (Set.mem_sInter.mp hx L hL)) B hBS
  refine ⟨K, hKB, hK.1.2.1, hK.1.2.2.1, hK.1.2.2.2.1, hK.1.2.2.2.2, ?_⟩
  intro L hLK hLn hLc hLv hLi
  exact hK.2 ⟨hLK.trans hKB, hLn, hLc, hLv, hLi⟩ hLK

end BoundedHochschild.KadisonRingrose

end

end OAI

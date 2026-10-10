import OAI.Analysis.KadisonKastler.WeakRowOrbit
import Mathlib.Order.Zorn

namespace OAI

/-! Minimal compact invariant families for normalized row averaging. -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance minimalRowFamilyOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance minimalRowFamilyStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

def RowInvariant {M : VonNeumannAlgebra H} {c : ℝ} (hc : 0 ≤ c)
    (K : Set (BoundedWeakAlgebraMap M c)) : Prop :=
  ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1),
    Set.MapsTo (boundedWeakRowAverage hc r hr) K K

theorem rowInvariant_sInter {M : VonNeumannAlgebra H} {c : ℝ} (hc : 0 ≤ c)
    (C : Set (Set (BoundedWeakAlgebraMap M c))) (hC : ∀ K ∈ C, RowInvariant hc K) :
    RowInvariant hc (⋂₀ C) := by
  intro n r hr F hF
  apply Set.mem_sInter.mpr
  intro K hK
  exact hC K hK n r hr (Set.mem_sInter.mp hF K hK)

theorem rowInvariant_closure_orbit {M : VonNeumannAlgebra H} {c : ℝ} (hc : 0 ≤ c)
    (F : BoundedWeakAlgebraMap M c) : RowInvariant hc (closure (boundedWeakRowOrbit F)) := by
  intro n r hr G hG
  exact closure_boundedWeakRowOrbit_invariant hc F r hr hG

/-- Compactness and Zorn's lemma give a genuine minimal invariant family.
This theorem does not assert that the family is a singleton. -/
theorem exists_minimal_row_family {M : VonNeumannAlgebra H} {c : ℝ} (hc : 0 ≤ c)
    (F : BoundedWeakAlgebraMap M c) :
    ∃ K : Set (BoundedWeakAlgebraMap M c), K ⊆ closure (boundedWeakRowOrbit F) ∧
      K.Nonempty ∧ IsClosed K ∧ RowInvariant hc K ∧
      ∀ L : Set (BoundedWeakAlgebraMap M c), L ⊆ K → L.Nonempty → IsClosed L →
        RowInvariant hc L → L = K := by
  classical
  let : CompactSpace (BoundedWeakAlgebraMap M c) :=
    isCompact_univ_iff.mp (isCompact_boundedWeakAlgebraMap M hc)
  let S : Set (Set (BoundedWeakAlgebraMap M c)) :=
    {K | K ⊆ closure (boundedWeakRowOrbit F) ∧ K.Nonempty ∧ IsClosed K ∧ RowInvariant hc K}
  have hstart : closure (boundedWeakRowOrbit F) ∈ S :=
    ⟨Set.Subset.refl _, closure_boundedWeakRowOrbit_nonempty F,
      isClosed_closure, rowInvariant_closure_orbit hc F⟩
  have hchain : ∀ C ⊆ S, IsChain (· ⊆ ·) C → C.Nonempty →
      ∃ K ∈ S, ∀ L ∈ C, K ⊆ L := by
    intro C hCS hC hne
    obtain ⟨K₀, hK₀⟩ := hne
    have : Nonempty C := ⟨⟨K₀, hK₀⟩⟩
    have hdir : DirectedOn (· ⊇ ·) C := by
      intro A hA B hB
      rcases hC.total hA hB with h | h
      · exact ⟨A, hA, Set.Subset.refl _, h⟩
      · exact ⟨B, hB, h, Set.Subset.refl _⟩
    have hnonempty : (⋂₀ C).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        hdir (fun K hK => (hCS hK).2.1)
        (fun K hK => (hCS hK).2.2.1.isCompact) (fun K hK => (hCS hK).2.2.1)
    refine ⟨⋂₀ C, ⟨?_, hnonempty, ?_, ?_⟩, ?_⟩
    · exact (Set.sInter_subset_of_mem hK₀).trans (hCS hK₀).1
    · exact isClosed_sInter (fun K hK => (hCS hK).2.2.1)
    · exact rowInvariant_sInter hc C (fun K hK => (hCS hK).2.2.2)
    · intro K hK
      exact Set.sInter_subset_of_mem hK
  obtain ⟨K, hKF, hmin⟩ := zorn_superset_nonempty S hchain _ hstart
  refine ⟨K, hKF, hmin.prop.2.1, hmin.prop.2.2.1, hmin.prop.2.2.2, ?_⟩
  intro L hLK hne hcl hinv
  exact hmin.eq_of_subset ⟨hLK.trans hmin.prop.1, hne, hcl, hinv⟩ hLK

end

end KadisonKastler

end OAI

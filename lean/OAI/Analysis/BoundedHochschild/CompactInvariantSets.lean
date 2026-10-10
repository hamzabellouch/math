import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

/-! Minimal compact invariant subsets and their open covers. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {A : Type u} [TopologicalSpace A] [T2Space A]
variable {G : Type v} [Group G]

omit [Group G] in
/-- A nonempty compact invariant set contains a minimal nonempty closed
invariant subset. -/
theorem exists_minimal_compact_invariant (T : G → A → A)
    (C : Set A) (hC : IsCompact C) (hne : C.Nonempty)
    (hinv : ∀ g, Set.MapsTo (T g) C C) :
    ∃ K : Set A, K ⊆ C ∧ K.Nonempty ∧ IsClosed K ∧
      (∀ g, Set.MapsTo (T g) K K) ∧
      ∀ L : Set A, L ⊆ K → L.Nonempty → IsClosed L →
        (∀ g, Set.MapsTo (T g) L L) → K ⊆ L := by
  classical
  let S : Set (Set A) := {K | K ⊆ C ∧ K.Nonempty ∧ IsClosed K ∧
    ∀ g, Set.MapsTo (T g) K K}
  have hCS : C ∈ S := ⟨Set.Subset.rfl, hne, hC.isClosed, hinv⟩
  obtain ⟨K, hKC, hK⟩ := zorn_superset_nonempty S (fun c hc hchain hcne => by
    have : Nonempty c := hcne.to_subtype
    have hn : (⋂₀ c).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (fun L hL J hJ => by
          rcases hchain.total hL hJ with h | h
          · exact ⟨L, hL, Set.Subset.rfl, h⟩
          · exact ⟨J, hJ, h, Set.Subset.rfl⟩)
        (fun L hL => (hc hL).2.1)
        (fun L hL => hC.of_isClosed_subset (hc hL).2.2.1 (hc hL).1)
        (fun L hL => (hc hL).2.2.1)
    refine ⟨⋂₀ c, ⟨?_, hn, ?_, ?_⟩, fun L hL => Set.sInter_subset_of_mem hL⟩
    · obtain ⟨L, hL⟩ := hcne
      exact (Set.sInter_subset_of_mem hL).trans (hc hL).1
    · exact isClosed_sInter (fun L hL => (hc hL).2.2.1)
    · intro g x hx
      apply Set.mem_sInter.mpr
      intro L hL
      exact (hc hL).2.2.2 g (Set.mem_sInter.mp hx L hL)) C hCS
  refine ⟨K, hKC, hK.1.2.1, hK.1.2.2.1, hK.1.2.2.2, ?_⟩
  intro L hLK hLn hLc hLi
  exact hK.2 ⟨hLK.trans hKC, hLn, hLc, hLi⟩ hLK

omit [T2Space A] in
/-- Every orbit in a minimal compact invariant set meets each nonempty
relatively open part of that set. -/
theorem minimal_invariant_open_cover (T : G → A → A)
    (hcont : ∀ g, Continuous (T g))
    (hone : ∀ x, T 1 x = x) (hmul : ∀ g h x, T (g * h) x = T g (T h x))
    (K : Set A) (hKc : IsClosed K) (hinv : ∀ g, Set.MapsTo (T g) K K)
    (hmin : ∀ L : Set A, L ⊆ K → L.Nonempty → IsClosed L →
      (∀ g, Set.MapsTo (T g) L L) → K ⊆ L)
    (U : Set A) (hU : IsOpen U) (hne : (K ∩ U).Nonempty) :
    K ⊆ ⋃ g, (T g) ⁻¹' U := by
  classical
  intro x hx
  by_contra hnot
  have hxnone : ∀ g, T g x ∉ U := by simpa only [Set.mem_iUnion, Set.mem_preimage, not_exists] using hnot
  let L : Set A := K ∩ ⋂ g, (T g) ⁻¹' Uᶜ
  have hLK : L ⊆ K := Set.inter_subset_left
  have hLn : L.Nonempty := ⟨x, hx, Set.mem_iInter.mpr hxnone⟩
  have hLc : IsClosed L := hKc.inter (isClosed_iInter (fun g => hU.isClosed_compl.preimage (hcont g)))
  have hLi : ∀ g, Set.MapsTo (T g) L L := by
    intro g y hy
    refine ⟨hinv g hy.1, Set.mem_iInter.mpr (fun h => ?_)⟩
    change T h (T g y) ∉ U
    rw [← hmul]
    exact Set.mem_iInter.mp hy.2 (h * g)
  obtain ⟨y, hyK, hyU⟩ := hne
  have hyL := hmin L hLK hLn hLc hLi hyK
  have hyout := Set.mem_iInter.mp hyL.2 1
  apply hyout
  simpa only [hone] using hyU

end KadisonRingrose
end BoundedHochschild

end

end OAI

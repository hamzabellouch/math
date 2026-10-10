import OAI.Analysis.SphereIsometry.CompactConvexFixedPoint
import OAI.Analysis.SphereIsometry.CondensingIteration
import OAI.Analysis.SphereIsometry.KuratowskiNested

namespace OAI

/-!
# Fixed points from a Kuratowski contraction

The compact invariant set is the intersection of the actual iterated
closed-convex images. All of its required properties are proved from the
original closed bounded convex invariant set and the all-subsets estimate.
-/

noncomputable section

namespace Tingley

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous self-map satisfying the actual all-subsets Kuratowski
contraction has a fixed point. No compactness premise on `C` is required. -/
theorem exists_fixedPoint_of_kuratowski_contraction
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconv : Convex ℝ C)
    {g : E → E} (hg : ContinuousOn g C) (hmap : MapsTo g C C)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hχ : ∀ H : Set E, H ⊆ C → chi (g '' H) ≤ γ * chi H) :
    ∃ x ∈ C, g x = x := by
  let K : Set E := ⋂ n, condensingSequence C g n
  have hdecay := condensingSequence_chi_tendsto_zero hclosed hconv hmap hbounded hγ0 hγ1 hχ
  obtain ⟨hKne, hKcompact⟩ := nonempty_isCompact_iInter_of_chi_tendsto_zero
    (condensingSequence C g)
    (condensingSequence_antitone hclosed hconv hmap)
    (condensingSequence_nonempty g hne)
    (condensingSequence_isClosed g hclosed)
    hbounded hdecay
  have hKconv : Convex ℝ K := convex_iInter (condensingSequence_convex g hconv)
  have hKC : K ⊆ C := by
    intro x hx
    exact (mem_iInter.mp hx) 0
  have hKmap : MapsTo g K K := by
    intro x hx
    apply mem_iInter.mpr
    intro n
    exact condensingSequence_mapsTo hclosed hconv hmap n ((mem_iInter.mp hx) n)
  obtain ⟨x, hx, hfix⟩ := exists_fixedPoint_of_isCompact_convex hKcompact hKne hKconv
    (hg.mono hKC) hKmap
  exact ⟨x, hKC hx, hfix⟩

/-- The subtype formulation measures the actual ambient images of subsets
of the carrier, and transports them through the explicit ambient map. -/
theorem continuous_condensing_fixedPoint
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconv : Convex ℝ C)
    (g : C → C) (hg : Continuous g) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hχ : ∀ H : Set C,
      chi ((fun x : C => (g x : E)) '' H) ≤ γ * chi (Subtype.val '' H)) :
    ∃ x, g x = x := by
  have hext : ∀ H : Set E, H ⊆ C →
      chi (extendSelfMap g '' H) ≤ γ * chi H := by
    intro H hHC
    let H' : Set C := {x | (x : E) ∈ H}
    have hdomain : (Subtype.val : C → E) '' H' = H := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hHC hx⟩, hx, rfl⟩
    have himage : (fun x : C => (g x : E)) '' H' = extendSelfMap g '' H := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(x : E), hx, extendSelfMap_coe g x⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hHC hx⟩, hx, (extendSelfMap_of_mem g (hHC hx)).symm⟩
    simpa only [hdomain, himage] using hχ H'
  obtain ⟨x, hx, hfix⟩ := exists_fixedPoint_of_kuratowski_contraction hne hclosed
    hbounded hconv (continuousOn_extendSelfMap hg) (extendSelfMap_mapsTo g) hγ0 hγ1 hext
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [extendSelfMap_of_mem g hx] at hfix
  exact hfix

end Tingley

end

end OAI

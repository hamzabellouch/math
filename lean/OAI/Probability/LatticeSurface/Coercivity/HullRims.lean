import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

lemma mem_rim_iff_star (B : Finset Vertex) (x : Vertex) :
    x∈rim B ↔ x∉B ∧ ∃ y∈B, star.Adj x y := by
  constructor
  · rintro ⟨hx,y,hy,h1,h2⟩
    exact ⟨hx,y,hy,⟨fun he => hx (he ▸ hy),h1,h2⟩⟩
  · rintro ⟨hx,y,hy,hxy⟩
    exact ⟨hx,y,hy,hxy.2.1,hxy.2.2⟩

lemma disjoint_hulls_rim (C D : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hD : D ⊆ box lo hi)
    (hsep : ∀ c∈C, ∀ d∈D, c≠d ∧ ¬star.Adj c d)
    (hdis : Disjoint (filled C lo hi) (filled D lo hi)) :
    Disjoint (rim (filled C lo hi)) (filled D lo hi:Set Vertex) := by
  apply Set.disjoint_left.mpr
  intro y hy hyD
  obtain ⟨_,c,hc,hyc⟩ := (mem_rim_iff_star C y).mp (filled_rim_subset C lo hi hC hy)
  have hcD : c∉filled D lo hi := Finset.disjoint_left.mp hdis (subset_filled C lo hi hC hc)
  have hcr : c∈rim (filled D lo hi) := (mem_rim_iff_star _ c).mpr ⟨hcD,y,hyD,hyc.symm⟩
  obtain ⟨_,d,hd,hcd⟩ := (mem_rim_iff_star D c).mp (filled_rim_subset D lo hi hD hcr)
  exact (hsep c hc d hd).2 hcd

lemma disjoint_hulls_separated (C D : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hD : D ⊆ box lo hi)
    (hsep : ∀ c∈C, ∀ d∈D, c≠d ∧ ¬star.Adj c d)
    (hdis : Disjoint (filled C lo hi) (filled D lo hi)) :
    ∀ x∈filled C lo hi, ∀ y∈filled D lo hi, x≠y ∧ ¬star.Adj x y := by
  intro x hx y hy
  have hyC : y∉filled C lo hi := Finset.disjoint_right.mp hdis hy
  refine ⟨fun he => hyC (he ▸ hx),?_⟩
  intro hxy
  have hr : y∈rim (filled C lo hi) := (mem_rim_iff_star _ y).mpr ⟨hyC,x,hx,hxy.symm⟩
  exact Set.disjoint_left.mp (disjoint_hulls_rim C D lo hi hC hD hsep hdis) hr hy

lemma exterior_independent (C : Finset Vertex) (lo hi lo' hi' : Vertex)
    (hC : C ⊆ box lo hi) (hC' : C ⊆ box lo' hi') :
    exterior C hi = exterior C hi' := by
  have hanc : safeReach C (anchor hi) (anchor hi') := by
    let top : ℤ := max hi.2 hi'.2+1
    have hc : ∀ j, (hi.1+1,j)∉C := by
      intro j hj
      have hh := mem_box.mp (hC hj)
      dsimp at hh;omega
    have hr : ∀ i, (i,top)∉C := by
      intro i hiC
      have hh := mem_box.mp (hC hiC)
      dsimp [top] at hh ⊢;omega
    have hc' : ∀ j, (hi'.1+1,j)∉C := by
      intro j hj
      have hh := mem_box.mp (hC' hj)
      dsimp at hh;omega
    exact safe_trans (safe_col C (hi.1+1) (hi.2+1) top hc)
      (safe_trans (safe_row C (hi.1+1) (hi'.1+1) top hr)
        (safe_col C (hi'.1+1) top (hi'.2+1) hc'))
  ext x
  exact ⟨fun h => safe_trans h hanc,fun h => safe_trans h (safe_symm hanc)⟩

lemma filled_independent (C : Finset Vertex) (lo hi lo' hi' : Vertex)
    (hC : C ⊆ box lo hi) (hC' : C ⊆ box lo' hi') :
    filled C lo hi = filled C lo' hi' := by
  ext x
  simp only [mem_filled C lo hi hC,mem_filled C lo' hi' hC',
    exterior_independent C lo hi lo' hi' hC hC']

lemma filled_in_any_box (C : Finset Vertex) (lo hi lo' hi' : Vertex)
    (hC : C ⊆ box lo hi) (hC' : C ⊆ box lo' hi') :
    filled C lo hi ⊆ box lo' hi' := by
  rw [filled_independent C lo hi lo' hi' hC hC']
  exact filled_subset_box C lo' hi'

end SparseHoles

end

end OAI

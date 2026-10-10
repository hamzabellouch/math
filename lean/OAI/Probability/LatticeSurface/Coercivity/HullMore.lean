import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleStar

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

lemma safe_mono {C D : Finset Vertex} (hCD : C ⊆ D) {x y : Vertex}
    (h : safeReach D x y) : safeReach C x y := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun z hz hzc => hp z hz (hCD hzc)⟩

lemma exterior_walk {C : Finset Vertex} {hi x : Vertex} (hx : x∈exterior C hi) :
    ∃ p : grid.Walk x (anchor hi), ∀ z∈p.support, z∈exterior C hi := by
  obtain ⟨p,hp⟩ := hx
  refine ⟨p,?_⟩
  intro z hz
  exact ⟨p.dropUntil z hz,fun w hw => hp w ((p.support_dropUntil_subset_support hz) hw)⟩

lemma filled_mono_hull (C D : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hD : D ⊆ box lo hi)
    (hCD : C ⊆ filled D lo hi) : filled C lo hi ⊆ filled D lo hi := by
  intro x hx
  rw [mem_filled D lo hi hD]
  intro he
  obtain ⟨p,hp⟩ := exterior_walk he
  apply (mem_filled C lo hi hC x).mp hx
  refine ⟨p,?_⟩
  intro z hz hzc
  exact (mem_filled D lo hi hD z).mp (hCD hzc) (hp z hz)

lemma filled_boundary (C : Finset Vertex) (lo hi : Vertex) (hC : C ⊆ box lo hi)
    {x y : Vertex} (hx : x∈filled C lo hi) (hy : y∉filled C lo hi)
    (hxy : grid.Adj x y) : x∈C := by
  by_contra h
  have he : y∈exterior C hi := by simpa only [mem_filled C lo hi hC,not_not] using hy
  exact (mem_filled C lo hi hC x).mp hx (exterior_adj h he hxy)

lemma safe_step_small {C : Finset Vertex} {x y : Vertex} (hx : x∉C) (hy : y∉C)
    (hxy : (x.1-y.1).natAbs+(x.2-y.2).natAbs ≤ 1) : safeReach C x y := by
  by_cases h : x=y
  · subst y;exact safe_refl C x hx
  · apply safe_adj hx hy
    change (x.1-y.1).natAbs+(x.2-y.2).natAbs=1
    have hn : (x.1-y.1).natAbs+(x.2-y.2).natAbs≠0 := by
      intro hh
      have h1 := Int.natAbs_eq_zero.mp (show (x.1-y.1).natAbs=0 by omega)
      have h2 := Int.natAbs_eq_zero.mp (show (x.2-y.2).natAbs=0 by omega)
      exact h (Prod.ext (by omega) (by omega))
    omega

lemma filled_rim_subset (C : Finset Vertex) (lo hi : Vertex) (hC : C ⊆ box lo hi) :
    rim (filled C lo hi) ⊆ rim C := by
  rintro y ⟨hy,x,hx,h1,h2⟩
  have hyc : y∉C := fun h => hy (subset_filled C lo hi hC h)
  refine ⟨hyc,?_⟩
  by_cases hxc : x∈C
  · exact ⟨x,hxc,h1,h2⟩
  · let z : Vertex := (y.1,x.2)
    have hzc : z∈C := by
      by_contra hzc
      have hxz : safeReach C x z := safe_step_small hxc hzc (by
        have h1' : (x.1-y.1).natAbs ≤ 1 := by rwa [← Int.natAbs_neg (x.1-y.1),neg_sub]
        simpa only [z,sub_self,Int.natAbs_zero,add_zero] using h1')
      have hzy : safeReach C z y := safe_step_small hzc hyc (by
        have h2' : (x.2-y.2).natAbs ≤ 1 := by rwa [← Int.natAbs_neg (x.2-y.2),neg_sub]
        simpa only [z,sub_self,Int.natAbs_zero,zero_add] using h2')
      have he : y∈exterior C hi := by simpa only [mem_filled C lo hi hC,not_not] using hy
      exact (mem_filled C lo hi hC x).mp hx (safe_trans (safe_trans hxz hzy) he)
    exact ⟨z,hzc,by simp [z],h2⟩

lemma star_mem_constant (C D : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hcD : (star.induce (D:Set Vertex)).Connected)
    (hsep : ∀ c∈C, ∀ d∈D, c≠d ∧ ¬star.Adj c d) :
    ∀ x∈D, ∀ y∈D, (x∈filled C lo hi ↔ y∈filled C lo hi) := by
  have hedge : ∀ x∈D, ∀ y∈D, star.Adj x y →
      (x∈filled C lo hi ↔ y∈filled C lo hi) := by
    intro x hx y hy hxy
    have hdirection : ∀ x∈D, ∀ y∈D, star.Adj x y →
        x∈filled C lo hi → y∈filled C lo hi := by
      intro a ha b hb hab haF
      by_contra hbF
      have hr : b∈rim (filled C lo hi) := ⟨hbF,a,haF,hab.symm.2.1,hab.symm.2.2⟩
      obtain ⟨_,c,hc,h1,h2⟩ := filled_rim_subset C lo hi hC hr
      have hh : star.Adj b c := ⟨(hsep c hc b hb).1.symm,h1,h2⟩
      exact (hsep c hc b hb).2 hh.symm
    exact ⟨hdirection x hx y hy hxy,hdirection y hy x hx hxy.symm⟩
  intro x hx y hy
  have he := constant_of_connected (star.induce (D:Set Vertex)) hcD
    (fun z => z.val∈filled C lo hi) (fun a b h => propext (hedge a a.property b b.property h))
    ⟨x,hx⟩ ⟨y,hy⟩
  exact he ▸ Iff.rfl

lemma cluster_dichotomy (C D : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hneD : D.Nonempty)
    (hcD : (star.induce (D:Set Vertex)).Connected)
    (hsep : ∀ c∈C, ∀ d∈D, c≠d ∧ ¬star.Adj c d) :
    D ⊆ filled C lo hi ∨ Disjoint D (filled C lo hi) := by
  classical
  obtain ⟨d,hd⟩ := hneD
  by_cases h : d∈filled C lo hi
  · exact Or.inl (fun x hx => (star_mem_constant C D lo hi hC hcD hsep d hd x hx).mp h)
  · right
    exact Finset.disjoint_left.mpr (fun x hx hxF => h
      ((star_mem_constant C D lo hi hC hcD hsep d hd x hx).mpr hxF))

lemma filled_laminar (C D : Finset Vertex) (lo hi : Vertex)
    (hC : C ⊆ box lo hi) (hD : D ⊆ box lo hi)
    (hneC : C.Nonempty) (hneD : D.Nonempty)
    (hcC : (star.induce (C:Set Vertex)).Connected)
    (hcD : (star.induce (D:Set Vertex)).Connected)
    (hsep : ∀ c∈C, ∀ d∈D, c≠d ∧ ¬star.Adj c d) :
    filled C lo hi ⊆ filled D lo hi ∨ filled D lo hi ⊆ filled C lo hi ∨
      Disjoint (filled C lo hi) (filled D lo hi) := by
  have hsep' : ∀ d∈D, ∀ c∈C, d≠c ∧ ¬star.Adj d c := by
    intro d hd c hc
    exact ⟨(hsep c hc d hd).1.symm,fun h => (hsep c hc d hd).2 h.symm⟩
  rcases cluster_dichotomy C D lo hi hC hneD hcD hsep with hDC|hDC
  · exact Or.inr (Or.inl (filled_mono_hull D C lo hi hD hC hDC))
  rcases cluster_dichotomy D C lo hi hD hneC hcC hsep' with hCD|hCD
  · exact Or.inl (filled_mono_hull C D lo hi hC hD hCD)
  right;right
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨c,hc,hpath⟩ := reach_cluster C hneC lo hi hC hxC
  obtain ⟨p⟩ := hpath
  let incl : grid.induce (filled C lo hi:Set Vertex) →g grid := ⟨Subtype.val,fun h => h⟩
  have hp : safeReach D x c := by
    refine ⟨p.map incl,?_⟩
    intro z hz hzd
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact Finset.disjoint_left.mp hDC hzd w.property
  have hcE : c∈exterior D hi := by
    have hcF := Finset.disjoint_left.mp hCD hc
    simpa only [mem_filled D lo hi hD,not_not] using hcF
  exact (mem_filled D lo hi hD x).mp hxD (safe_trans hp hcE)

end SparseHoles

end

end OAI

import OAI.Probability.FirstPassage.SquareLoops
import OAI.Probability.FirstPassage.OrientedCompactness
import OAI.Probability.FirstPassage.SeparatedSelection

namespace OAI

namespace PlanarFPP
open Finset

theorem exists_enclosing_squareLoop (S : Finset Vertex) (h0 : (0 : Vertex) ∈ S) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : SquareLoop m,
      c.NoRepeatedSides ∧ c.winding ≠ 0 ∧ ∀ i, IsBoundarySide S (c.side i) := by
  classical
  obtain ⟨x,hn,hpos,_,hnext,hw⟩ := exists_boundary_cycle S h0
  let es := (boundaryPerm S).toList x
  have hlen : 0 < es.length := hpos
  have : NeZero es.length := ⟨Nat.ne_of_gt hlen⟩
  let c : SquareLoop es.length :=
    { side := fun i => (es.get i).val
      follows := by
        intro i
        have hh := hnext (es.get i) (List.get_mem es i)
        change (es.next es[i.val] (List.get_mem es i)).val.tail = es[i.val].val.head at hh
        rw [List.next_getElem es hn i.val i.isLt] at hh
        simpa only [List.get_eq_getElem, finRotate_apply, Fin.val_add,
          Fin.val_one', Nat.add_mod_mod] using hh }
  refine ⟨es.length,hlen,c,?_,?_,?_⟩
  · exact Subtype.val_injective.comp hn.injective_get
  · change (∑ i : Fin es.length, (es.get i).val.rayCross) ≠ 0
    have hh : (∑ i : Fin es.length, (es.get i).val.rayCross) =
        ∑ e ∈ es.toFinset, e.val.rayCross := by
      rw [List.sum_toFinset _ hn, ← Fin.sum_ofFn]
      have hmap : List.map (fun e : BoundarySide S => e.val.rayCross) (List.ofFn es.get) =
          List.ofFn (fun i => (es.get i).val.rayCross) := List.map_ofFn
      simpa only [List.ofFn_get] using congrArg List.sum hmap.symm
    rw [hh]
    exact hw
  · intro i
    exact (mem_boundarySides S _).mp (es.get i).property

theorem exists_enclosing_squareLoop_unoriented (S : Finset Vertex) (h0 : (0 : Vertex) ∈ S) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : SquareLoop m,
      c.winding ≠ 0 ∧ (∀ i, IsBoundarySide S (c.side i)) ∧
      Function.Injective (fun i => (c.side i).2.edge (c.side i).tail) := by
  obtain ⟨m,hm,c,hc,hw,hb⟩ := exists_enclosing_squareLoop S h0
  refine ⟨m,hm,c,hw,hb,?_⟩
  intro i j hij
  exact hc (boundary_dualEdge_injective S _ _ (hb i) (hb j) hij)

theorem SquareLoop.badSites_bad {m : ℕ} (c : SquareLoop m)
    (S : Finset Vertex) (G : Vertex → Prop)
    (hb : ∀ i, IsBoundarySide S (c.side i))
    (hforward : ∀ q ∈ S, G q → q+(1,0) ∈ S ∧ q+(0,1) ∈ S) :
    ∀ q ∈ c.badSites, ¬G q := by
  intro q hq hg
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
  have hf := hforward _ (hb i).1 hg
  have hout := (hb i).2
  rcases (mem_filter.mp hi).2 with hd | hd
  · exact hout (by simpa [hd,Step.outward,Step.right,Step.delta] using hf.1)
  · exact hout (by simpa [hd,Step.outward,Step.right,Step.delta] using hf.2)

theorem no_infinite_path_enclosing_contour (G : Vertex → Prop) (k : ℕ)
    (h : ¬infiniteOrientedPath G 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : SquareLoop m,
      c.NoRepeatedSides ∧ c.winding ≠ 0 ∧
      (∀ q ∈ c.badSites, ¬G q) ∧
      ∃ T : Finset Vertex, T ⊆ c.badSites ∧
        Set.Pairwise (↑T : Set Vertex) (fun p q => ¬latticeNear k p q) ∧
        m ≤ 8*(2*k+1)^2*T.card := by
  classical
  let hf := orientedReachable_finite_of_no_infinite_path G 0 h
  let S := hf.toFinset
  have hS (q : Vertex) : q ∈ S ↔ q ∈ orientedReachable G 0 := hf.mem_toFinset
  have h0 : (0 : Vertex) ∈ S := (hS 0).mpr (orientedReachable_origin G 0)
  obtain ⟨m,hm,c,hc,hw,hb⟩ := exists_enclosing_squareLoop S h0
  refine ⟨m,hm,c,hc,hw,?_,?_⟩
  · apply c.badSites_bad S G hb
    intro q hq hg
    have hh := orientedReachable_forward G 0 q ((hS q).mp hq) hg
    exact ⟨(hS _).mpr hh.1,(hS _).mpr hh.2⟩
  · obtain ⟨T,hT,hpair,hcard⟩ := lattice_separated_selection c.badSites k
    refine ⟨T,hT,hpair,?_⟩
    have hh := c.length_le_eight_badSites hc
    nlinarith

end PlanarFPP

end OAI

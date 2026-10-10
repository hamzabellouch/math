import OAI.Combinatorics.Ramsey.CycleClique.Construction.Monotonicity

namespace OAI

/-!
# The exceptional triangle Ramsey number

The elementary six-vertex argument and the complementary pentagons prove
`R(C₃,K₃) = 6`, the exceptional clause of the manuscript's main theorem.
-/

namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V}

theorem hasCycle_three_of_edges {x y z : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) : HasCycle G 3 := by
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hxy.ne, hyz.ne, hzx.ne]
  · intro i
    fin_cases i
    · simpa [cycleNext] using hxy
    · simpa [cycleNext] using hyz
    · simpa [cycleNext] using hzx

theorem hasIndependent_three_of_distinct_nonadjacent {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxy' : ¬ G.Adj x y) (hxz' : ¬ G.Adj x z) (hyz' : ¬ G.Adj y z) :
    HasIndependent G 3 := by
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j
    have hyx' : ¬ G.Adj y x := fun h => hxy' h.symm
    have hzx' : ¬ G.Adj z x := fun h => hxz' h.symm
    have hzy' : ¬ G.Adj z y := fun h => hyz' h.symm
    fin_cases i <;> fin_cases j <;> simp_all

/-- Every graph on six vertices has a triangle or three independent vertices. -/
theorem triangle_upper : RamseyProperty 3 3 6 := by
  intro G
  classical
  let red : Finset (Fin 5) := Finset.univ.filter (fun i => G.Adj 0 i.succ)
  let blue : Finset (Fin 5) := Finset.univ.filter (fun i => ¬ G.Adj 0 i.succ)
  have hsum : red.card + blue.card = 5 := by
    simpa [red, blue] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin 5 => G.Adj 0 i.succ)
  have hlarge : 2 < red.card ∨ 2 < blue.card := by omega
  rcases hlarge with hr | hb
  · obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hr
    have hx' : G.Adj 0 x.succ := (Finset.mem_filter.mp hx).2
    have hy' : G.Adj 0 y.succ := (Finset.mem_filter.mp hy).2
    have hz' : G.Adj 0 z.succ := (Finset.mem_filter.mp hz).2
    by_cases hxy' : G.Adj x.succ y.succ
    · exact Or.inl (hasCycle_three_of_edges hx' hxy' hy'.symm)
    by_cases hxz' : G.Adj x.succ z.succ
    · exact Or.inl (hasCycle_three_of_edges hx' hxz' hz'.symm)
    by_cases hyz' : G.Adj y.succ z.succ
    · exact Or.inl (hasCycle_three_of_edges hy' hyz' hz'.symm)
    exact Or.inr (hasIndependent_three_of_distinct_nonadjacent ((Fin.succ_injective 5).ne hxy)
      ((Fin.succ_injective 5).ne hxz) ((Fin.succ_injective 5).ne hyz) hxy' hxz' hyz')
  · obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hb
    have hx' : ¬ G.Adj 0 x.succ := (Finset.mem_filter.mp hx).2
    have hy' : ¬ G.Adj 0 y.succ := (Finset.mem_filter.mp hy).2
    have hz' : ¬ G.Adj 0 z.succ := (Finset.mem_filter.mp hz).2
    by_cases hxy' : G.Adj x.succ y.succ
    · by_cases hxz' : G.Adj x.succ z.succ
      · by_cases hyz' : G.Adj y.succ z.succ
        · exact Or.inl (hasCycle_three_of_edges hxy' hyz' hxz'.symm)
        · exact Or.inr (hasIndependent_three_of_distinct_nonadjacent (Fin.succ_ne_zero y).symm
            (Fin.succ_ne_zero z).symm ((Fin.succ_injective 5).ne hyz) hy' hz' hyz')
      · exact Or.inr (hasIndependent_three_of_distinct_nonadjacent (Fin.succ_ne_zero x).symm
          (Fin.succ_ne_zero z).symm ((Fin.succ_injective 5).ne hxz) hx' hz' hxz')
    · exact Or.inr (hasIndependent_three_of_distinct_nonadjacent (Fin.succ_ne_zero x).symm
        (Fin.succ_ne_zero y).symm ((Fin.succ_injective 5).ne hxy) hx' hy' hxy')

/-- The pentagon coloring: red edges have cyclic difference one. -/
def pentagon : SimpleGraph (Fin 5) where
  Adj x y := (x.val + 1) % 5 = y.val ∨ (y.val + 1) % 5 = x.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro x h; rcases h with h | h <;> omega⟩

instance : DecidableRel pentagon.Adj := by unfold pentagon; infer_instance

private theorem pentagon_no_triangle :
    ∀ x y z : Fin 5, pentagon.Adj x y → pentagon.Adj y z → ¬ pentagon.Adj z x := by
  decide

private theorem pentagon_no_independent_triple :
    ∀ x y z : Fin 5, x ≠ y → x ≠ z → y ≠ z →
      ¬ pentagon.Adj x y → ¬ pentagon.Adj x z → pentagon.Adj y z := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- Five vertices do not force a monochromatic triangle. -/
theorem triangle_lower : ¬ RamseyProperty 3 3 5 := by
  intro h
  rcases h pentagon with ⟨f, hf, he⟩ | ⟨f, hf, he⟩
  · have h01 : pentagon.Adj (f 0) (f 1) := by simpa [cycleNext] using he 0
    have h12 : pentagon.Adj (f 1) (f 2) := by simpa [cycleNext] using he 1
    have h20 : pentagon.Adj (f 2) (f 0) := by simpa [cycleNext] using he 2
    exact pentagon_no_triangle _ _ _ h01 h12 h20
  · exact he 1 2 (pentagon_no_independent_triple (f 0) (f 1) (f 2)
      (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide)) (he 0 1) (he 0 2))

end CycleClique.Construction

end OAI

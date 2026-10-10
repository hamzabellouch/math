import OAI.Combinatorics.ContingencyTables.Rooted.ForestCut

namespace OAI

/-!
# Actual bipartite cell forests and their completion intervals

The graph vertices are the original row and column labels. Capacities
are attached to unordered row-column edges. The deletion-component cut
is constructed from the maximizing forest, so the hypotheses of the
physical cut estimate follow from actual graph properties.
-/

namespace ContingencyTables.ForestCapacity

open scoped BigOperators Classical
open SimpleGraph
open MaximumForest ForestCut

variable {I J : Type*} [Fintype I] [Fintype J]

def cellAdj (small : I → J → Bool) : I⊕J → I⊕J → Prop
  | .inl i,.inr j => small i j=false
  | .inr j,.inl i => small i j=false
  | _,_ => False

def cellGraph (small : I → J → Bool) : SimpleGraph (I⊕J) where
  Adj := cellAdj small
  symm := ⟨by intro v w; cases v <;> cases w <;> exact id⟩
  loopless := ⟨by intro v; cases v <;> exact id⟩

def pairCapacity (b : I → J → ℕ) : I⊕J → I⊕J → ℕ
  | .inl i,.inr j => b i j
  | .inr j,.inl i => b i j
  | _,_ => 0

def capacity (b : I → J → ℕ) : Sym2 (I⊕J) → ℕ :=
  Sym2.lift ⟨pairCapacity b,by intro v w; cases v <;> cases w <;> rfl⟩

omit [Fintype I] [Fintype J] in
@[simp] lemma capacity_cell (b : I → J → ℕ) (i : I) (j : J) :
    capacity b s(Sum.inl i,Sum.inr j)=b i j := rfl

omit [Fintype I] [Fintype J] in
lemma cell_edge_injective : Function.Injective
    (fun a : I×J => s(Sum.inl a.1,Sum.inr a.2)) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  simpa only [Sym2.eq_iff,Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,
    Sum.inl_ne_inr,Sum.inr_ne_inl,false_and,or_false] using h

noncomputable def treeCell (T : SimpleGraph (I⊕J)) (i : I) (j : J) : Bool :=
  decide (T.Adj (.inl i) (.inr j))

/-- The actual maximum-forest cut gives the source's displacement and
interval bounds for every solution of the selected nonroot equations. -/
theorem completion_interval (small : I → J → Bool) (b : I → J → ℕ)
    (T : SimpleGraph (I⊕J)) (hTG : T≤cellGraph small) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph (I⊕J), F≤cellGraph small → F.IsAcyclic →
      weight F (capacity b)≤weight T (capacity b))
    (i₀ : I) (j₀ : J) (ht : T.Adj (.inl i₀) (.inr j₀)) (root : I⊕J)
    (hroot : T.Reachable root (.inl i₀))
    (x q z X : I → J → ℝ) (d : ℝ) (W : ℕ)
    (hd : 1≤d) (hcard : (Fintype.card I*Fintype.card J:ℕ)≤d)
    (hlarge : ∀ i j, small i j=false → W≤b i j ∧ 1≤b i j)
    (hsmall : ∀ i j, small i j=true → b i j<W ∧
      (0≤x i j ∧ x i j≤b i j) ∧ (0≤q i j ∧ q i j≤b i j))
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j)
    (hfree : ∀ i j, small i j=false → treeCell T i j=false →
      0≤z i j ∧ z i j≤b i j+1)
    (hr : ∀ i, T.Reachable root (.inl i) → Sum.inl i≠root → rowDifference small x z X i=0)
    (hc : ∀ j, T.Reachable root (.inr j) → Sum.inr j≠root → columnDifference small q z X j=0) :
    -10*d*b i₀ j₀≤z i₀ j₀ ∧ z i₀ j₀≤10*d*b i₀ j₀ := by
  let t : Sym2 (I⊕J) := s(Sum.inl i₀,Sum.inr j₀)
  let D := T.deleteEdges {t}
  obtain ⟨r,hrr,hrootSide,hcross⟩ := exists_root_avoiding_side T hT ht root hroot
  let rowU : I → Bool := fun i => side D r (.inl i)
  let colU : J → Bool := fun j => side D r (.inr j)
  have hs₀ : small i₀ j₀=false := hTG ht
  have hB : (1:ℝ)≤b i₀ j₀ := by exact_mod_cast (hlarge i₀ j₀ hs₀).2
  have hdisp : |z i₀ j₀-X i₀ j₀|≤4*d*b i₀ j₀ := by
    apply displacement_bound small (treeCell T) rowU colU x q z X
      (fun i j => (b i j:ℝ)) i₀ j₀ d hcard hB hs₀ hcross
    · intro i hi
      change side D r (.inl i)=true at hi
      apply hr i
      · have hri : D.Reachable r (.inl i) := by
          simpa only [side,decide_eq_true_eq] using hi
        exact hrr.trans (hri.mono
          (T.deleteEdges_le {t}))
      · intro he
        have hbad : side D r root=true := by simpa only [he] using hi
        exact Bool.false_ne_true (hrootSide.symm.trans hbad)
    · intro j hj
      change side D r (.inr j)=true at hj
      apply hc j
      · have hrj : D.Reachable r (.inr j) := by
          simpa only [side,decide_eq_true_eq] using hj
        exact hrr.trans (hrj.mono
          (T.deleteEdges_le {t}))
      · intro he
        have hbad : side D r root=true := by simpa only [he] using hj
        exact Bool.false_ne_true (hrootSide.symm.trans hbad)
    · exact hX
    · intro i j hs
      have hcap : b i j≤b i₀ j₀ := (Nat.le_of_lt (hsmall i j hs).1).trans
        (hlarge i₀ j₀ hs₀).1
      exact ⟨by exact_mod_cast hcap,(hsmall i j hs).2⟩
    · intro i j htree hne
      apply side_eq_of_tree_edge T t r
      · exact of_decide_eq_true htree
      · exact fun he => hne (cell_edge_injective he)
    · intro i j hs htree
      refine ⟨hfree i j hs htree,?_⟩
      intro hcut
      have hgraph : (cellGraph small).Adj (.inl i) (.inr j) := hs
      have hcap := crossing_free_edge_le (cellGraph small) T (capacity b)
        hTG hT hmax t (by simpa [t] using ht) r hgraph
        (by simpa only [treeCell,decide_eq_false_iff_not] using htree) hcut
      exact_mod_cast hcap
  exact physical_interval_of_displacement d (b i₀ j₀) (X i₀ j₀) (z i₀ j₀)
    hd (Nat.cast_nonneg _) (hX i₀ j₀) hdisp

end ContingencyTables.ForestCapacity

end OAI

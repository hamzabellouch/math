import OAI.MeasureTheory.Falconer.Radial.CoarsePlateFilter

namespace OAI

/-! # Exact product-cell structure of every finite coarse plate filter -/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.descendant_subset_take {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (j : ℕ) :
    (Q.descendant p).carrier ⊆ (Q.descendant (p.take j)).carrier := by
  have he : Q.descendant p = (Q.descendant (p.take j)).descendant (p.drop j) := by
    rw [← Q.descendant_append,List.take_append_drop]
  rw [he]
  exact (Q.descendant (p.take j)).descendant_subset (p.drop j)

theorem DyadicCube.same_fine_cell_coarse {d J j : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) (hp : p.length = J) (hq : q.length = j) (hj : j ≤ J)
    {x x' : Space d} (hx : x ∈ (Q.descendant p).carrier)
    (hx' : x' ∈ (Q.descendant p).carrier) (hxq : x ∈ (Q.descendant q).carrier) :
    x' ∈ (Q.descendant q).carrier := by
  have htake : (p.take j).length = j := by simp only [List.length_take,hp,min_eq_left hj]
  have heq : p.take j = q := by
    by_contra hn
    exact Set.disjoint_left.mp (Q.descendants_disjoint (htake.trans hq.symm) hn)
      (Q.descendant_subset_take p j hx) hxq
  rw [← heq]
  exact Q.descendant_subset_take p j hx'

theorem heavyPlateCellPairs_fine_invariant {d J j : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (r m : ℝ) (p q : List (Fin d → Bool))
    (hp : p.length = J) (hq : q.length = J) (hj : j ≤ J)
    {x y x' y' : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (hy : y ∈ (Q.descendant q).carrier)
    (hx' : x' ∈ (Q.descendant p).carrier) (hy' : y' ∈ (Q.descendant q).carrier)
    (hxy : (x,y) ∈ heavyPlateCellPairs ρ Q j r m) :
    (x',y') ∈ heavyPlateCellPairs ρ Q j r m := by
  obtain ⟨a,ha,b,hb,hhit,hxa,hyb⟩ := (mem_heavyPlateCellPairs_iff ρ Q j r m x y).mp hxy
  exact (mem_heavyPlateCellPairs_iff ρ Q j r m x' y').mpr
    ⟨a,ha,b,hb,hhit,Q.same_fine_cell_coarse p a hp ((mem_cubePaths d j a).mp ha) hj hx hx' hxa,
      Q.same_fine_cell_coarse q b hq ((mem_cubePaths d j b).mp hb) hj hy hy' hyb⟩

theorem coarsePlateFilter_fine_invariant {d J : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ : ℕ) (r m : ℕ → ℝ) (p q : List (Fin d → Bool))
    (hp : p.length = J) (hq : q.length = J) {x y x' y' : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (hy : y ∈ (Q.descendant q).carrier)
    (hx' : x' ∈ (Q.descendant p).carrier) (hy' : y' ∈ (Q.descendant q).carrier)
    (hxy : (x,y) ∈ coarsePlateFilter ρ Q j₀ J r m) :
    (x',y') ∈ coarsePlateFilter ρ Q j₀ J r m := by
  refine ⟨⟨Q.descendant_subset p hx',Q.descendant_subset q hy'⟩,?_⟩
  intro hex
  obtain ⟨j,hj,hxy'⟩ := mem_iUnion₂.mp hex
  apply hxy.2
  exact mem_iUnion₂.mpr ⟨j,hj,heavyPlateCellPairs_fine_invariant ρ Q (r j) (m j)
    p q hp hq (Finset.mem_Icc.mp hj).2 hx' hy' hx hy hxy'⟩

theorem coarsePlateFilter_product_cells {d : ℕ} (ρ : Measure (Space d))
    (Q : DyadicCube d) (j₀ J : ℕ) (r m : ℕ → ℝ) :
    ∃ T : Finset (List (Fin d → Bool) × List (Fin d → Bool)),
      T ⊆ (cubePaths d J).product (cubePaths d J) ∧
      coarsePlateFilter ρ Q j₀ J r m =
        ⋃ pq ∈ T, (Q.descendant pq.1).carrier ×ˢ (Q.descendant pq.2).carrier := by
  classical
  let T := ((cubePaths d J).product (cubePaths d J)).filter
    (fun pq => (Q.descendant pq.1).carrier ×ˢ (Q.descendant pq.2).carrier ⊆
      coarsePlateFilter ρ Q j₀ J r m)
  refine ⟨T,Finset.filter_subset _ _,?_⟩
  apply Subset.antisymm
  · rintro ⟨x,y⟩ hxy
    obtain ⟨p,hp,hx⟩ := Q.mem_descendant_at_depth J hxy.1.1
    obtain ⟨q,hq,hy⟩ := Q.mem_descendant_at_depth J hxy.1.2
    apply mem_iUnion₂.mpr
    refine ⟨(p,q),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp,hq⟩,?_⟩,hx,hy⟩
    rintro ⟨x',y'⟩ ⟨hx',hy'⟩
    exact coarsePlateFilter_fine_invariant ρ Q j₀ r m p q
      ((mem_cubePaths d J p).mp hp) ((mem_cubePaths d J q).mp hq) hx hy hx' hy' hxy
  · intro xy hxy
    obtain ⟨pq,hpq,hxy⟩ := mem_iUnion₂.mp hxy
    exact (Finset.mem_filter.mp hpq).2 hxy

end Falconer

end OAI

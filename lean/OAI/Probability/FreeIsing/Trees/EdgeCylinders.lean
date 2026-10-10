import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

private theorem edge_adj_symm {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) : treeAdj v u := Or.symm h

private theorem edge_adj_ne {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) : u ≠ v := by
  intro heq
  subst v
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩ <;>
    have hl := congrArg List.length hc <;> simp at hl

theorem connectedFinset_pair_of_adj {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) : ConnectedFinset ({u, v} : Finset (TreeVertex d)) := by
  classical
  constructor
  · simp
  · intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by simp, by simp, h⟩
    · exact Relation.ReflTransGen.single ⟨by simp, by simp, edge_adj_symm h⟩
    · exact Relation.ReflTransGen.refl

theorem inducedEdges_pair_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hl : u.1.length < v.1.length) :
    inducedEdges ({u, v} : Finset (TreeVertex d)) = {(u, v)} := by
  classical
  ext ⟨a,b⟩
  rw [show inducedEdges ({u,v} : Finset (TreeVertex d)) =
    (({u,v} : Finset (TreeVertex d)).product {u,v}).filter
      (fun e => treeAdj e.1 e.2 ∧ e.1.1.length < e.2.1.length) from rfl]
  rw [Finset.mem_filter]
  rw [Finset.product_eq_sprod, Finset.mem_product]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab, hlen⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · omega
    · exact ⟨rfl, rfl⟩
    · omega
    · omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨Or.inl rfl, Or.inr rfl⟩, h, hl⟩

theorem freeCylinderWeight_pair_of_length_lt {d : ℕ} (theta : ℝ)
    {u v : TreeVertex d} (h : treeAdj u v) (hl : u.1.length < v.1.length)
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta {u,v} eta =
      ENNReal.ofReal ((1 + (if eta u = eta v then theta else -theta)) / 4) := by
  classical
  rw [freeCylinderWeight, inducedEdges_pair_of_length_lt h hl]
  simp only [Finset.prod_singleton]
  congr 1
  ring

private theorem edge_adj_length_lt_or {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) : u.1.length < v.1.length ∨ v.1.length < u.1.length := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left
    simp [hc]
  · right
    simp [hc]

theorem freeCylinderWeight_pair {d : ℕ} (theta : ℝ)
    {u v : TreeVertex d} (h : treeAdj u v) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta {u,v} eta =
      ENNReal.ofReal ((1 + (if eta u = eta v then theta else -theta)) / 4) := by
  classical
  rcases edge_adj_length_lt_or h with hl | hl
  · exact freeCylinderWeight_pair_of_length_lt theta h hl eta
  · rw [Finset.pair_comm]
    simpa only [eq_comm] using
      freeCylinderWeight_pair_of_length_lt theta (edge_adj_symm h) hl eta

theorem HasFreeIsingLaw.edge_cylinder {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    {u v : TreeVertex d} (huv : treeAdj u v) (a b : IsingSpin) :
    mu {x | x u = a ∧ x v = b} =
      ENNReal.ofReal ((1 + (if a = b then theta else -theta)) / 4) := by
  classical
  let eta : TreeVertex d → IsingSpin := fun w => if w = u then a else b
  have h := hmu {u,v} (connectedFinset_pair_of_adj huv) eta
  rw [freeCylinderWeight_pair theta huv eta] at h
  have hne : v ≠ u := (edge_adj_ne huv).symm
  simpa [eta, hne] using h

end Problem367

end

end OAI

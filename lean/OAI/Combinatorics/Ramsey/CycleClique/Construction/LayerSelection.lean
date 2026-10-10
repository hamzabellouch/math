import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayerStructure

namespace OAI

/-!
# Choosing the minimum dense induced subgraph in a layer

The two selection lemmas make the minimum-order choice in manuscript
Proposition `clq:layer-interface` and supply exactly the local minimality
premises used by the expansion and connectivity arguments.
-/

namespace CycleClique.Construction
theorem indepNum_le_of_induced_injection {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ {x y}, H.Adj (f x) (f y) → G.Adj x y) : G.indepNum ≤ H.indepNum := by
  classical
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  let J : Finset W := I.map ⟨f, hf⟩
  have hJ : H.IsIndepSet (J : Set W) := by
    intro x hx y hy hxy hadjxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hI.isIndepSet ha hb (fun h => hxy (congrArg f h)) (hadj hadjxy)
  simpa [J, hI.card_eq] using hJ.card_le_indepNum

theorem indepNum_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : G.indepNum = H.indepNum := by
  apply Nat.le_antisymm
  · exact indepNum_le_of_induced_injection e e.injective (fun h => e.map_adj_iff.mp h)
  · exact indepNum_le_of_induced_injection e.symm e.symm.injective
      (fun h => e.symm.map_adj_iff.mp h)

private noncomputable def nestedInduceIso {V : Type*} (G : SimpleGraph V) (Y : Finset V)
    (Z : Finset Y) :
    (G.induce (Y : Set V)).induce (Z : Set Y) ≃g
      G.induce ((Z.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset V) : Set V) := by
  classical
  let Z' : Finset V := Z.map ⟨Subtype.val, Subtype.val_injective⟩
  let f : Z → Z' := fun z => ⟨z.val.val, Finset.mem_map.mpr ⟨z.val, z.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Z' => z.val) h
  have hs : Function.Surjective f := by
    intro z
    obtain ⟨a, ha, heq⟩ := Finset.mem_map.mp z.property
    refine ⟨⟨a, ha⟩, ?_⟩
    exact Subtype.ext heq
  refine { Equiv.ofBijective f ⟨hf, hs⟩ with map_rel_iff' := ?_ }
  rfl

/-- The minimum-order weakly dense subgraph of a layer (even `k`). -/
theorem exists_minimal_dense_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    {s : ℕ} (D : Finset V) (hD : D.Nonempty)
    (hdense : s * (G.induce (D : Set V)).indepNum ≤ D.card) :
    ∃ Y : Finset V, Y ⊆ D ∧ Y.Nonempty ∧
      s * (G.induce (Y : Set V)).indepNum ≤ Y.card ∧
      ∀ Z : Finset Y, Z.Nonempty → Z.card < Y.card →
        Z.card < s * ((G.induce (Y : Set V)).induce (Z : Set Y)).indepNum := by
  classical
  let P : Finset V → Prop := fun Y => Y ⊆ D ∧ Y.Nonempty ∧
    s * (G.induce (Y : Set V)).indepNum ≤ Y.card
  have hex : ∃ n, ∃ Y : Finset V, Y.card = n ∧ P Y :=
    ⟨D.card, D, rfl, Finset.Subset.refl _, hD, hdense⟩
  obtain ⟨Y, hYcard, hYP⟩ := Nat.find_spec hex
  have hmin : ∀ X : Finset V, P X → Y.card ≤ X.card := by
    intro X hX
    rw [hYcard]
    exact Nat.find_min' hex ⟨X, rfl, hX⟩
  refine ⟨Y, hYP.1, hYP.2.1, hYP.2.2, ?_⟩
  intro Z hZ hZcard
  by_contra hnot
  let Z' : Finset V := Z.map ⟨Subtype.val, Subtype.val_injective⟩
  have hZ'D : Z' ⊆ D := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hz
    exact hYP.1 a.property
  have hZ'ne : Z'.Nonempty := by simpa [Z'] using hZ
  have hIso := indepNum_eq_of_iso (nestedInduceIso G Y Z)
  have hZ'dense : s * (G.induce (Z' : Set V)).indepNum ≤ Z'.card := by
    rw [← hIso]
    simpa [Z'] using (show s * ((G.induce (Y : Set V)).induce (Z : Set Y)).indepNum ≤ Z.card by omega)
  have hm := hmin Z' ⟨hZ'D, hZ'ne, hZ'dense⟩
  have hc : Z'.card = Z.card := Finset.card_map _
  omega

/-- The minimum-order strictly dense subgraph of a layer (odd `k`). -/
theorem exists_minimal_dense_odd {V : Type*} [Fintype V] {G : SimpleGraph V}
    {s : ℕ} (D : Finset V) (hD : D.Nonempty)
    (hdense : s * (G.induce (D : Set V)).indepNum < D.card) :
    ∃ Y : Finset V, Y ⊆ D ∧ Y.Nonempty ∧
      s * (G.induce (Y : Set V)).indepNum < Y.card ∧
      ∀ Z : Finset Y, Z.Nonempty → Z.card < Y.card →
        Z.card ≤ s * ((G.induce (Y : Set V)).induce (Z : Set Y)).indepNum := by
  classical
  let P : Finset V → Prop := fun Y => Y ⊆ D ∧ Y.Nonempty ∧
    s * (G.induce (Y : Set V)).indepNum < Y.card
  have hex : ∃ n, ∃ Y : Finset V, Y.card = n ∧ P Y :=
    ⟨D.card, D, rfl, Finset.Subset.refl _, hD, hdense⟩
  obtain ⟨Y, hYcard, hYP⟩ := Nat.find_spec hex
  have hmin : ∀ X : Finset V, P X → Y.card ≤ X.card := by
    intro X hX
    rw [hYcard]
    exact Nat.find_min' hex ⟨X, rfl, hX⟩
  refine ⟨Y, hYP.1, hYP.2.1, hYP.2.2, ?_⟩
  intro Z hZ hZcard
  by_contra hnot
  let Z' : Finset V := Z.map ⟨Subtype.val, Subtype.val_injective⟩
  have hZ'D : Z' ⊆ D := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hz
    exact hYP.1 a.property
  have hZ'ne : Z'.Nonempty := by simpa [Z'] using hZ
  have hIso := indepNum_eq_of_iso (nestedInduceIso G Y Z)
  have hZ'dense : s * (G.induce (Z' : Set V)).indepNum < Z'.card := by
    rw [← hIso]
    simpa [Z'] using (show s * ((G.induce (Y : Set V)).induce (Z : Set Y)).indepNum < Z.card by omega)
  have hm := hmin Z' ⟨hZ'D, hZ'ne, hZ'dense⟩
  have hc : Z'.card = Z.card := Finset.card_map _
  omega

end CycleClique.Construction

end OAI

import Mathlib

namespace OAI

noncomputable section

namespace Problem310.TreePreorder

/-- Edge paths in the complete ordered `q`-ary tree, in depth-first preorder. -/
def edgePaths (q : ℕ) : ℕ → List (List (Fin q))
  | 0 => []
  | d + 1 => (List.finRange q).flatMap fun i =>
      [i] :: (edgePaths q d).map (List.cons i)

/-- Number of edges in the complete tree. -/
def edgeCount (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => q * (1 + edgeCount q d)

@[simp] theorem edgePaths_zero (q : ℕ) : edgePaths q 0 = [] := rfl

@[simp] theorem edgePaths_succ (q d : ℕ) :
    edgePaths q (d + 1) = (List.finRange q).flatMap (fun i =>
      [i] :: (edgePaths q d).map (List.cons i)) := rfl

/-- Exactly the nonempty paths of length at most the tree depth occur. -/
theorem mem_edgePaths_iff (q d : ℕ) (p : List (Fin q)) :
    p ∈ edgePaths q d ↔ p ≠ [] ∧ p.length ≤ d := by
  induction d generalizing p with
  | zero => simp [edgePaths]
  | succ d ih =>
      cases p with
      | nil => simp [edgePaths]
      | cons i p =>
          simp only [edgePaths, List.mem_flatMap, List.mem_finRange, true_and,
            List.mem_cons, List.cons.injEq, List.mem_map, List.length_cons,
            ]
          constructor
          · rintro ⟨j, h | ⟨p', hp', h⟩⟩
            · rcases h with ⟨rfl, rfl⟩
              simp
            · rcases h with ⟨rfl, rfl⟩
              have hlen := (ih p').mp hp'
              exact ⟨by simp, Nat.succ_le_succ hlen.2⟩
          · intro hp
            by_cases he : p = []
            · subst p
              exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩
            · exact ⟨i, Or.inr ⟨p, (ih p).mpr ⟨he, by omega⟩, ⟨rfl, rfl⟩⟩⟩

@[simp] theorem length_edgePaths (q d : ℕ) :
    (edgePaths q d).length = edgeCount q d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [edgePaths, edgeCount, List.length_flatMap, ih, add_comm]

/-- Each child block consists entirely of paths with that child as first entry. -/
theorem mem_childBlock_prefix (q d : ℕ) (i : Fin q) (p : List (Fin q))
    (hp : p ∈ [i] :: (edgePaths q d).map (List.cons i)) :
    ∃ s, p = i :: s := by
  rcases List.mem_cons.mp hp with h | h
  · exact ⟨[], h⟩
  · obtain ⟨s, hs, h⟩ := List.mem_map.mp h
    exact ⟨s, h.symm⟩

/-- The preorder contains no duplicate edge path. -/
theorem nodup_edgePaths (q d : ℕ) : (edgePaths q d).Nodup := by
  induction d with
  | zero => simp [edgePaths]
  | succ d ih =>
      rw [edgePaths_succ, List.nodup_flatMap]
      constructor
      · intro i hi
        rw [List.nodup_cons]
        constructor
        · intro hm
          obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
          have hp0 : p = [] := (List.cons.inj heq).2
          subst p
          simp [mem_edgePaths_iff] at hp
        · exact ih.map (by intro a b h; exact (List.cons.inj h).2)
      · apply (List.nodup_finRange q).imp
        intro i j hij p hp hq
        obtain ⟨s, rfl⟩ := mem_childBlock_prefix q d i p hp
        obtain ⟨t, heq⟩ := mem_childBlock_prefix q d j (i :: s) hq
        exact hij (List.cons.inj heq).1

/-- The finite type of tree edges, represented by nonempty bounded-depth paths. -/
def Edge (q d : ℕ) := {p : List (Fin q) // p ∈ edgePaths q d}

instance (q d : ℕ) : Fintype (Edge q d) := by
  classical
  unfold Edge
  exact Fintype.ofFinset (edgePaths q d).toFinset (by intro p; exact List.mem_toFinset)

@[simp] theorem edge_nonempty {q d : ℕ} (e : Edge q d) : e.val ≠ [] :=
  ((mem_edgePaths_iff q d e.val).mp e.property).1

theorem edge_length_le {q d : ℕ} (e : Edge q d) : e.val.length ≤ d :=
  ((mem_edgePaths_iff q d e.val).mp e.property).2

/-- Convert a nonempty bounded path into the finite edge type. -/
def mkEdge {q d : ℕ} (p : List (Fin q)) (hne : p ≠ []) (hlen : p.length ≤ d) :
    Edge q d := ⟨p, (mem_edgePaths_iff q d p).mpr ⟨hne, hlen⟩⟩

@[simp] theorem mkEdge_val {q d : ℕ} (p : List (Fin q))
    (hne : p ≠ []) (hlen : p.length ≤ d) :
    (mkEdge p hne hlen).val = p := rfl

/-- The preorder gives the canonical enumeration of finite tree edges. -/
def edgeEquivFin (q d : ℕ) : Edge q d ≃ Fin (edgeCount q d) :=
  (List.Nodup.getEquiv (edgePaths q d) (nodup_edgePaths q d)).symm.trans
    (finCongr (length_edgePaths q d))

@[simp] theorem card_Edge (q d : ℕ) : Fintype.card (Edge q d) = edgeCount q d := by
  rw [Fintype.card_congr (edgeEquivFin q d), Fintype.card_fin]

/-- Edges corresponding to appending a child at a strict internal node. -/
def childEdge {q d : ℕ} (P : List (Fin q)) (hP : P.length < d) (i : Fin q) :
    Edge q d := mkEdge (P ++ [i]) (by simp) (by simp; omega)

@[simp] theorem childEdge_val {q d : ℕ} (P : List (Fin q))
    (hP : P.length < d) (i : Fin q) : (childEdge P hP i).val = P ++ [i] := rfl

/-- Child edges at fixed parent are distinct. -/
theorem childEdge_injective {q d : ℕ} (P : List (Fin q)) (hP : P.length < d) :
    Function.Injective (childEdge P hP) := by
  intro i j hij
  have h : P ++ [i] = P ++ [j] := congrArg Subtype.val hij
  simpa using h

/-- The incoming edge of a subtree and all its descendants form one consecutive
block in the depth-first edge preorder. -/
theorem subtree_block (q d : ℕ) (p : List (Fin q)) (hne : p ≠ []) (hlen : p.length ≤ d) :
    ∃ pre post : List (List (Fin q)),
      edgePaths q d = pre ++
        (p :: (edgePaths q (d - p.length)).map (fun s => p ++ s)) ++ post := by
  induction d generalizing p with
  | zero =>
      have : p = [] := List.length_eq_zero_iff.mp (by omega)
      exact (hne this).elim
  | succ d ih =>
      cases p with
      | nil => exact (hne rfl).elim
      | cons i p =>
          have hip : i ∈ List.finRange q := List.mem_finRange i
          obtain ⟨L, R, hLR⟩ := List.mem_iff_append.mp hip
          let block := fun j : Fin q => [j] :: (edgePaths q d).map (List.cons j)
          have hsplit : edgePaths q (d + 1) =
              L.flatMap block ++ block i ++ R.flatMap block := by
            rw [edgePaths_succ, hLR]
            simp [block, List.flatMap_append, List.append_assoc]
          by_cases hp : p = []
          · subst p
            refine ⟨L.flatMap block, R.flatMap block, ?_⟩
            simpa [block] using hsplit
          · have hpl : p.length ≤ d := by simpa using hlen
            obtain ⟨A, B, hAB⟩ := ih p hp hpl
            refine ⟨L.flatMap block ++ [i] :: A.map (List.cons i),
              B.map (List.cons i) ++ R.flatMap block, ?_⟩
            rw [hsplit]
            simp only [block, hAB, List.map_append, List.map_cons,
              List.map_map, Function.comp_def, List.length_cons, Nat.add_sub_add_right]
            simp only [List.cons_append, List.append_assoc]

/-- In the subtree decomposition, the prefix length is exactly the preorder index. -/
theorem subtree_block_index (q d : ℕ) (p : List (Fin q))
    (hne : p ≠ []) (hlen : p.length ≤ d) :
    ∃ pre post : List (List (Fin q)),
      edgePaths q d = pre ++
        (p :: (edgePaths q (d - p.length)).map (fun s => p ++ s)) ++ post ∧
      pre.length = (edgePaths q d).idxOf p := by
  obtain ⟨pre, post, heq⟩ := subtree_block q d p hne hlen
  refine ⟨pre, post, heq, ?_⟩
  have hnod : (pre ++ p ::
      ((edgePaths q (d - p.length)).map (fun s => p ++ s) ++ post)).Nodup := by
    simpa [heq, List.append_assoc] using nodup_edgePaths q d
  have hnot : p ∉ pre := by
    intro hp
    have hdis := (List.nodup_append.mp hnod).2.2
    exact hdis p hp p (by simp) rfl
  simp [heq, List.append_assoc, List.idxOf_append_of_notMem hnot]

end Problem310.TreePreorder

end

end OAI

import OAI.Combinatorics.MatrixRemoval.AnchorGroups
import OAI.Combinatorics.MatrixRemoval.AnchorProperties
import OAI.Combinatorics.MatrixRemoval.HostTwins

namespace OAI

/-!
# Group coordinates of a canonical host anchor copy

One-mode anchor rigidity, the entries of `Construction.host`, and distinct
rows and columns of `anchor64` force exhaustion of the anchor groups.
The two axes use independent key functions, with no global order instance
on the raw carrier.
-/

universe uK uKR uKC

namespace Problem348.Construction.AnchorGroups

/-- The row groups of a one-mode anchor copy are exactly their pattern indices.
Only the within-mode comparison property of the chosen row order is needed. -/
theorem row_representatives {h : ℕ} {K : Type uK} [LinearOrder K]
    (key : Position h → K) (r c : Fin 64 → Position h) (t : Mode h)
    (hr : StrictMono (fun i => key (r i)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hmode : ∀ i, ∃ u x, r i = Sum.inl (t, u, x))
    (horder : ∀ u v : Fin 64, ∀ x y : Fin (2 ^ h),
      key (Sum.inl (t,u,x)) < key (Sum.inl (t,v,y)) → u ≤ v) :
    ∃ x : Fin 64 → Fin (2 ^ h), ∀ i, r i = Sum.inl (t,i,x i) := by
  classical
  choose g x hx using hmode
  have hmono : Monotone g := by
    intro i j hij
    rcases eq_or_lt_of_le hij with e | hij
    · subst j
      exact le_rfl
    · apply horder (g i) (g j) (x i) (x j)
      simpa only [hx i, hx j] using hr hij
  have heq : ∀ i, g i = i :=
    Problem348.AnchorGroups.group_eq_index anchor64 host r c g
      anchor64_rows_injective hcopy
      (by
        intro i j hij z
        rw [hx i, hx j, ← hij]
        exact host_anchor_row_twin t (g i) (x i) (x j) (c z)) hmono
  refine ⟨x, fun i => ?_⟩
  simpa only [heq i] using hx i

/-- The analogous conclusion for the independently ordered column axis. -/
theorem column_representatives {h : ℕ} {K : Type uK} [LinearOrder K]
    (key : Position h → K) (r c : Fin 64 → Position h) (t : Mode h)
    (hc : StrictMono (fun j => key (c j)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hmode : ∀ j, ∃ v y, c j = Sum.inl (t, v, y))
    (horder : ∀ u v : Fin 64, ∀ x y : Fin (2 ^ h),
      key (Sum.inl (t,u,x)) < key (Sum.inl (t,v,y)) → u ≤ v) :
    ∃ y : Fin 64 → Fin (2 ^ h), ∀ j, c j = Sum.inl (t,j,y j) := by
  classical
  choose g y hy using hmode
  have hmono : Monotone g := by
    intro i j hij
    rcases eq_or_lt_of_le hij with e | hij
    · subst j
      exact le_rfl
    · apply horder (g i) (g j) (y i) (y j)
      simpa only [hy i, hy j] using hc hij
  have heq : ∀ j, g j = j :=
    Problem348.AnchorGroups.group_eq_index (fun j i => anchor64 i j)
      (fun b a => host a b) c r g anchor64_columns_injective
      (fun j i => hcopy i j)
      (by
        intro i j hij z
        rw [hy i, hy j, ← hij]
        exact host_anchor_column_twin t (g i) (y i) (y j) (r z)) hmono
  refine ⟨y, fun j => ?_⟩
  simpa only [heq j] using hy j

/-- Both axes of the canonical anchor copy use every group in its prescribed
order, with independent choices of the within-group offsets. -/
theorem representatives {h : ℕ} {KR : Type uKR} {KC : Type uKC}
    [LinearOrder KR] [LinearOrder KC]
    (rowKey : Position h → KR) (colKey : Position h → KC)
    (r c : Fin 64 → Position h) (t : Mode h)
    (hr : StrictMono (fun i => rowKey (r i)))
    (hc : StrictMono (fun j => colKey (c j)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hrowmode : ∀ i, ∃ u x, r i = Sum.inl (t,u,x))
    (hcolmode : ∀ j, ∃ v y, c j = Sum.inl (t,v,y))
    (hroworder : ∀ u v : Fin 64, ∀ x y : Fin (2 ^ h),
      rowKey (Sum.inl (t,u,x)) < rowKey (Sum.inl (t,v,y)) → u ≤ v)
    (hcolorder : ∀ u v : Fin 64, ∀ x y : Fin (2 ^ h),
      colKey (Sum.inl (t,u,x)) < colKey (Sum.inl (t,v,y)) → u ≤ v) :
    ∃ x y : Fin 64 → Fin (2 ^ h),
      (∀ i, r i = Sum.inl (t,i,x i)) ∧ (∀ j, c j = Sum.inl (t,j,y j)) := by
  obtain ⟨x, hx⟩ := row_representatives rowKey r c t hr hcopy hrowmode hroworder
  obtain ⟨y, hy⟩ := column_representatives colKey r c t hc hcopy hcolmode hcolorder
  exact ⟨x, y, hx, hy⟩

end Problem348.Construction.AnchorGroups

end OAI

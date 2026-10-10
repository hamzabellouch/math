import OAI.Combinatorics.MatrixRemoval.OrderedHost
import OAI.Combinatorics.MatrixRemoval.HostAnchorGroups

namespace OAI

/-!
# Prescribed anchor coordinates in the actual ordered host

The independent enumerations satisfy `OrderedHost.row_anchor_strictMono`
and `column_anchor_strictMono`, giving the order premises of one-mode group
exhaustion without a default order instance on the raw Position sum type.
-/

universe uI uO uK

namespace Problem348.OrderedHost

open Construction

private theorem group_le_of_ordered_representatives
    {I : Type uI} {O : Type uO} {K : Type uK} [LinearOrder I] [LinearOrder K]
    (key : I → O → K)
    (hmono : ∀ f : I → O, StrictMono (fun i => key i (f i)))
    (u v : I) (x y : O) (hxy : key u x < key v y) : u ≤ v := by
  by_contra hnot
  have hvu : v < u := lt_of_not_ge hnot
  have hne : u ≠ v := ne_of_gt hvu
  have hback := hmono (fun i => if i = v then y else x) hvu
  simp only [ite_eq_right hne] at hback
  exact lt_asymm hxy hback

/-- Increasing rows in one mode have nondecreasing anchor group indices. -/
theorem row_anchor_group_le {h : ℕ} (t : Mode h) (u v : Fin 64)
    (x y : Fin (2 ^ h))
    (hxy : rowIndex h (Sum.inl (t,u,x)) < rowIndex h (Sum.inl (t,v,y))) :
    u ≤ v :=
  group_le_of_ordered_representatives
    (fun i a => rowIndex h (Sum.inl (t,i,a)))
    (row_anchor_strictMono t) u v x y hxy

/-- The analogous group-order implication for the actual column enumeration. -/
theorem column_anchor_group_le {h : ℕ} (t : Mode h) (u v : Fin 64)
    (x y : Fin (2 ^ h))
    (hxy : columnIndex h (Sum.inl (t,u,x)) < columnIndex h (Sum.inl (t,v,y))) :
    u ≤ v :=
  group_le_of_ordered_representatives
    (fun i a => columnIndex h (Sum.inl (t,i,a)))
    (column_anchor_strictMono t) u v x y hxy

/-- Mode rigidity locates the prefix in one mode, forcing its exact group
coordinates in the concrete ordered host. No additional group, twin, density,
or order hypotheses are required. -/
theorem anchor_representatives_of_one_mode {h : ℕ}
    (r c : Fin 64 → Position h) (t : Mode h)
    (hr : StrictMono (fun i => rowIndex h (r i)))
    (hc : StrictMono (fun j => columnIndex h (c j)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hrowmode : ∀ i, ∃ u x, r i = Sum.inl (t,u,x))
    (hcolmode : ∀ j, ∃ v y, c j = Sum.inl (t,v,y)) :
    ∃ x y : Fin 64 → Fin (2 ^ h),
      (∀ i, r i = Sum.inl (t,i,x i)) ∧ (∀ j, c j = Sum.inl (t,j,y j)) := by
  exact Construction.AnchorGroups.representatives (rowIndex h) (columnIndex h)
    r c t hr hc hcopy hrowmode hcolmode
    (row_anchor_group_le t) (column_anchor_group_le t)

end Problem348.OrderedHost

end OAI

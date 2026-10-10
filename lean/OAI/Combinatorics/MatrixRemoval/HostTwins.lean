import OAI.Combinatorics.MatrixRemoval.Host

namespace OAI

/-!
Concrete twin-position facts for anchor rigidity in the flat-class host.
-/

namespace Problem348.Construction

/-- Changing the representative inside an anchor row group changes no entry. -/
theorem host_anchor_row_twin {h : ℕ} (t : Mode h) (u : Fin 64)
    (x y : Fin (2 ^ h)) (c : Position h) :
    host (Sum.inl (t,u,x)) c = host (Sum.inl (t,u,y)) c := by
  rcases c with a | (v | d) <;> rfl

/-- Changing the representative inside an anchor column group changes no entry. -/
theorem host_anchor_column_twin {h : ℕ} (t : Mode h) (v : Fin 64)
    (x y : Fin (2 ^ h)) (r : Position h) :
    host r (Sum.inl (t,v,x)) = host r (Sum.inl (t,v,y)) := by
  rcases r with a | (v | d) <;> rfl

/-- All dummy rows, including their anchor incidences, have equal signatures. -/
theorem host_dummy_row_twin {h : ℕ} (x y : Fin (2 ^ h)) (c : Position h) :
    host (Sum.inr (Sum.inr x)) c = host (Sum.inr (Sum.inr y)) c := by
  rcases c with a | (v | d) <;> rfl

/-- All dummy columns, including their anchor incidences, have equal signatures. -/
theorem host_dummy_column_twin {h : ℕ} (x y : Fin (2 ^ h)) (r : Position h) :
    host r (Sum.inr (Sum.inr x)) = host r (Sum.inr (Sum.inr y)) := by
  rcases r with a | (v | d) <;> rfl

/-- The anchor-group label forgets only the coordinate within a group. -/
def anchorGroup {h : ℕ} : Position h → Option (Mode h × Fin 64)
  | Sum.inl (t,u,_) => some (t,u)
  | Sum.inr _ => none

/-- A group-label equality is enough to prove that two full row signatures agree. -/
theorem host_rows_eq_of_anchorGroup {h : ℕ} {r r' : Position h}
    {t : Mode h} {u : Fin 64}
    (hr : anchorGroup r = some (t,u)) (hr' : anchorGroup r' = some (t,u)) :
    ∀ c, host r c = host r' c := by
  rcases r with ⟨t₁,u₁,x⟩ | r
  · rcases r' with ⟨t₂,u₂,y⟩ | r'
    · simp only [anchorGroup, Option.some.injEq, Prod.mk.injEq] at hr hr'
      rcases hr with ⟨rfl,rfl⟩
      rcases hr' with ⟨rfl,rfl⟩
      exact host_anchor_row_twin _ _ x y
    · simp [anchorGroup] at hr'
  · simp [anchorGroup] at hr

/-- The same group-label criterion on the column axis. -/
theorem host_columns_eq_of_anchorGroup {h : ℕ} {c c' : Position h}
    {t : Mode h} {u : Fin 64}
    (hc : anchorGroup c = some (t,u)) (hc' : anchorGroup c' = some (t,u)) :
    ∀ r, host r c = host r c' := by
  rcases c with ⟨t₁,u₁,x⟩ | c
  · rcases c' with ⟨t₂,u₂,y⟩ | c'
    · simp only [anchorGroup, Option.some.injEq, Prod.mk.injEq] at hc hc'
      rcases hc with ⟨rfl,rfl⟩
      rcases hc' with ⟨rfl,rfl⟩
      exact host_anchor_column_twin _ _ x y
    · simp [anchorGroup] at hc'
  · simp [anchorGroup] at hc

/-- A true anchor--anchor entry forces the two modes to coincide. -/
theorem mode_eq_of_host_anchor_true {h : ℕ} {t t' : Mode h}
    {u v : Fin 64} {x y : Fin (2 ^ h)}
    (he : host (Sum.inl (t,u,x)) (Sum.inl (t',v,y)) = true) : t = t' := by
  by_contra hne
  simp [host, hne] at he

/-- In any one mode a non-anchor row can be one in at most one anchor group. -/
theorem nonanchor_row_one_group_unique {h : ℕ}
    (r : VariablePosition h ⊕ Fin (2 ^ h)) (t : Mode h)
    (u v : Fin 64) (x y : Fin (2 ^ h))
    (hu : host (Sum.inr r) (Sum.inl (t,u,x)) = true)
    (hv : host (Sum.inr r) (Sum.inl (t,v,y)) = true) : u = v := by
  have hu' : (u.val = 0 ∧ rowRole t 0 (Sum.inr r)) ∨
      (u.val = 1 ∧ rowRole t 1 (Sum.inr r)) := by
    simpa only [host, decide_eq_true_eq] using hu
  have hv' : (v.val = 0 ∧ rowRole t 0 (Sum.inr r)) ∨
      (v.val = 1 ∧ rowRole t 1 (Sum.inr r)) := by
    simpa only [host, decide_eq_true_eq] using hv
  rcases hu' with ⟨hu₀, hr₀⟩ | ⟨hu₁, hr₁⟩ <;>
    rcases hv' with ⟨hv₀, hs₀⟩ | ⟨hv₁, hs₁⟩
  · exact Fin.ext (hu₀.trans hv₀.symm)
  · exact False.elim (rowRole_disjoint t (Sum.inr r) ⟨hr₀, hs₁⟩)
  · exact False.elim (rowRole_disjoint t (Sum.inr r) ⟨hs₀, hr₁⟩)
  · exact Fin.ext (hu₁.trans hv₁.symm)

/-- In any one mode a non-anchor column can be one in at most one anchor group. -/
theorem nonanchor_column_one_group_unique {h : ℕ}
    (c : VariablePosition h ⊕ Fin (2 ^ h)) (t : Mode h)
    (u v : Fin 64) (x y : Fin (2 ^ h))
    (hu : host (Sum.inl (t,u,x)) (Sum.inr c) = true)
    (hv : host (Sum.inl (t,v,y)) (Sum.inr c) = true) : u = v := by
  have hu' : (u.val = 0 ∧ colRole t 0 (Sum.inr c)) ∨
      (u.val = 1 ∧ colRole t 1 (Sum.inr c)) := by
    simpa only [host, decide_eq_true_eq] using hu
  have hv' : (v.val = 0 ∧ colRole t 0 (Sum.inr c)) ∨
      (v.val = 1 ∧ colRole t 1 (Sum.inr c)) := by
    simpa only [host, decide_eq_true_eq] using hv
  rcases hu' with ⟨hu₀, hr₀⟩ | ⟨hu₁, hr₁⟩ <;>
    rcases hv' with ⟨hv₀, hs₀⟩ | ⟨hv₁, hs₁⟩
  · exact Fin.ext (hu₀.trans hv₀.symm)
  · exact False.elim (colRole_disjoint t (Sum.inr c) ⟨hr₀, hs₁⟩)
  · exact False.elim (colRole_disjoint t (Sum.inr c) ⟨hs₀, hr₁⟩)
  · exact Fin.ext (hu₁.trans hv₁.symm)

end Problem348.Construction

end OAI

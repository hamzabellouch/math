import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.BodyRoles

namespace OAI

/-!
# Body-role extraction for the canonical host

Anchor traces determine body roles in the actual `Construction.host` table.
-/

namespace Problem348.Construction

theorem rowRole_of_anchor_trace {h : ℕ} (t : Mode h) (r : Position h)
    (z : Fin 64 → Fin (2 ^ h)) (b : Fin 2)
    (hsig : ∀ v : Fin 64,
      host r (Sum.inl (t, v, z v)) = decide (v.val = b.val)) :
    rowRole t b r := by
  rcases r with ⟨t', u, a⟩ | r
  · by_cases ht : t' = t
    · subst t'
      have heq : (fun v => anchor64 u v) =
          (fun v : Fin 64 => decide (v.val = b.val)) := by
        funext v
        simpa [host] using hsig v
      exact False.elim (BodySignatures52.anchor64_row_ne_body_signature u b heq)
    · have heq : (fun _ : Fin 64 => false) =
          (fun v : Fin 64 => decide (v.val = b.val)) := by
        funext v
        simpa [host, ht] using hsig v
      exact False.elim (BodySignatures52.zero_ne_body_signature b heq)
  · fin_cases b
    · have hv := hsig (0 : Fin 64)
      simpa [host] using hv
    · have hv := hsig (1 : Fin 64)
      simpa [host] using hv

theorem colRole_of_anchor_trace {h : ℕ} (t : Mode h) (c : Position h)
    (z : Fin 64 → Fin (2 ^ h)) (b : Fin 2)
    (hsig : ∀ u : Fin 64,
      host (Sum.inl (t, u, z u)) c = decide (u.val = b.val)) :
    colRole t b c := by
  rcases c with ⟨t', v, a⟩ | c
  · by_cases ht : t = t'
    · subst t'
      have heq : (fun u => anchor64 u v) =
          (fun u : Fin 64 => decide (u.val = b.val)) := by
        funext u
        simpa [host] using hsig u
      exact False.elim (BodySignatures52.anchor64_col_ne_body_signature v b heq)
    · have heq : (fun _ : Fin 64 => false) =
          (fun u : Fin 64 => decide (u.val = b.val)) := by
        funext u
        simpa [host, ht] using hsig u
      exact False.elim (BodySignatures52.zero_ne_body_signature b heq)
  · fin_cases b
    · have hu := hsig (0 : Fin 64)
      simpa [host] using hu
    · have hu := hsig (1 : Fin 64)
      simpa [host] using hu

/-- Exact converse, useful also when constructing a guarded anchor frame. -/
theorem anchor_trace_of_rowRole {h : ℕ} (t : Mode h) (r : Position h)
    (z : Fin 64 → Fin (2 ^ h)) (b : Fin 2) (hr : rowRole t b r) :
    ∀ v : Fin 64, host r (Sum.inl (t, v, z v)) = decide (v.val = b.val) := by
  have hd := rowRole_disjoint t r
  rcases r with a | r
  · simp [rowRole] at hr
  · fin_cases b
    · have hn : ¬ rowRole t 1 (Sum.inr r) := fun h1 => hd ⟨hr, h1⟩
      intro v
      simp [host, hn]
      exact fun _ => hr
    · have hn : ¬ rowRole t 0 (Sum.inr r) := fun h0 => hd ⟨h0, hr⟩
      intro v
      simp [host, hn]
      exact fun _ => hr

theorem anchor_trace_of_colRole {h : ℕ} (t : Mode h) (c : Position h)
    (z : Fin 64 → Fin (2 ^ h)) (b : Fin 2) (hc : colRole t b c) :
    ∀ u : Fin 64, host (Sum.inl (t, u, z u)) c = decide (u.val = b.val) := by
  have hd := colRole_disjoint t c
  rcases c with a | c
  · simp [colRole] at hc
  · fin_cases b
    · have hn : ¬ colRole t 1 (Sum.inr c) := fun h1 => hd ⟨hc, h1⟩
      intro u
      simp [host, hn]
      exact fun _ => hc
    · have hn : ¬ colRole t 0 (Sum.inr c) := fun h0 => hd ⟨h0, hc⟩
      intro u
      simp [host, hn]
      exact fun _ => hc

/-- Raw matching version, independent of any enumeration or order on the axes. -/
theorem host_body_roles_of_matching {h : ℕ}
    (r c : Fin 66 → Position h)
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j)
    (t : Mode h) (zr zc : Fin 64 → Fin (2 ^ h))
    (hrows : ∀ u, r (BodySignatures52.anchorIndex u) = Sum.inl (t, u, zr u))
    (hcols : ∀ v, c (BodySignatures52.anchorIndex v) = Sum.inl (t, v, zc v))
    (b : Fin 2) :
    rowRole t b (r (BodySignatures52.bodyIndex b)) ∧
      colRole t b (c (BodySignatures52.bodyIndex b)) := by
  constructor
  · apply rowRole_of_anchor_trace t _ zc b
    intro v
    rw [← hcols v]
    exact (hmatch _ _).trans (BodySignatures52.fixedH_body_anchor b v)
  · apply colRole_of_anchor_trace t _ zr b
    intro u
    rw [← hrows u]
    exact (hmatch _ _).trans (BodySignatures52.fixedH_anchor_body u b)

/-- The lower-right four cells of any raw matching copy form exactly P. -/
theorem host_body_entries_of_matching {h : ℕ}
    (r c : Fin 66 → Position h)
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j) :
    host (r (BodySignatures52.bodyIndex 0)) (c (BodySignatures52.bodyIndex 0)) = true ∧
    host (r (BodySignatures52.bodyIndex 0)) (c (BodySignatures52.bodyIndex 1)) = false ∧
    host (r (BodySignatures52.bodyIndex 1)) (c (BodySignatures52.bodyIndex 0)) = true ∧
    host (r (BodySignatures52.bodyIndex 1)) (c (BodySignatures52.bodyIndex 1)) = true := by
  simp only [hmatch, BodySignatures52.fixedH_body_body]
  decide

/-- An actual ordered copy in a transported canonical host has the
two prescribed body roles, once anchor rigidity pins its prefix. -/
theorem host_body_roles_of_copy {h n : ℕ} {A : BinaryMatrix n}
    (row col : Fin n → Position h)
    (hA : ∀ i j, A i j = host (row i) (col j))
    {rc : IncreasingMap 66 n × IncreasingMap 66 n}
    (hcopy : rc ∈ orderedCopies fixedH A)
    (t : Mode h) (zr zc : Fin 64 → Fin (2 ^ h))
    (hrows : ∀ u, row (rc.1.val (BodySignatures52.anchorIndex u)) =
      Sum.inl (t, u, zr u))
    (hcols : ∀ v, col (rc.2.val (BodySignatures52.anchorIndex v)) =
      Sum.inl (t, v, zc v))
    (b : Fin 2) :
    rowRole t b (row (rc.1.val (BodySignatures52.bodyIndex b))) ∧
      colRole t b (col (rc.2.val (BodySignatures52.bodyIndex b))) := by
  constructor
  · apply rowRole_of_anchor_trace t _ zc b
    intro v
    rw [← hcols v, ← hA]
    exact BodySignatures52.copy_body_row_signature hcopy b v
  · apply colRole_of_anchor_trace t _ zr b
    intro u
    rw [← hrows u, ← hA]
    exact BodySignatures52.copy_body_col_signature hcopy b u

end Problem348.Construction

end OAI

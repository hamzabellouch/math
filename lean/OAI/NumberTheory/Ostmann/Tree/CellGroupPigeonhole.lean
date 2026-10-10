import OAI.NumberTheory.Ostmann.Tree.CellListPigeonhole

namespace OAI

/-! # Fixing every cell group at the cost of the total number of labels -/

namespace Ostmann

def encodeCellGroups : List (List ℕ) → List ℕ
  | [] => []
  | w :: ws => w.length :: (w ++ encodeCellGroups ws)

def decodeCellGroups : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | _ + 1, [] => []
  | r + 1, n :: xs => xs.take n :: decodeCellGroups r (xs.drop n)

theorem decode_encodeCellGroups (ws : List (List ℕ)) :
    decodeCellGroups ws.length (encodeCellGroups ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [encodeCellGroups, decodeCellGroups, ih]

theorem encodeCellGroups_injective_of_length {ws vs : List (List ℕ)}
    (hlen : ws.length = vs.length) (he : encodeCellGroups ws = encodeCellGroups vs) : ws = vs := by
  calc
    ws = decodeCellGroups ws.length (encodeCellGroups ws) := (decode_encodeCellGroups ws).symm
    _ = decodeCellGroups vs.length (encodeCellGroups vs) := by rw [hlen, he]
    _ = vs := decode_encodeCellGroups vs

theorem encodeCellGroups_length (ws : List (List ℕ)) :
    (encodeCellGroups ws).length = (ws.map List.length).sum + ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [encodeCellGroups, List.length_cons, List.length_append,
      List.map_cons, List.sum_cons, ih]; omega

theorem encodeCellGroups_entries (ws : List (List ℕ)) (N B : ℕ)
    (hl : ∀ w ∈ ws, w.length ≤ N) (he : ∀ w ∈ ws, ∀ h ∈ w, h ≤ B) :
    ∀ h ∈ encodeCellGroups ws, h ≤ max N B := by
  induction ws with
  | nil => simp [encodeCellGroups]
  | cons w ws ih =>
    intro h hh
    simp only [encodeCellGroups, List.mem_cons, List.mem_append] at hh
    rcases hh with rfl | hw | hws
    · exact (hl w (by simp)).trans (le_max_left _ _)
    · exact (he w (by simp) h hw).trans (le_max_right _ _)
    · exact ih (fun v hv => hl v (by simp [hv]))
        (fun v hv => he v (by simp [hv])) h hws

/-- Length-prefix coding retains the group boundaries while using only one
extra entry per group. Thus the pigeonhole cost depends on the total label
count, rather than the product of the separate group-length bounds. -/
theorem common_cell_groups (E : Finset ℕ) (hE : E.Nonempty) (r N B : ℕ)
    (ws : ℕ → List (List ℕ))
    (hr : ∀ a ∈ E, (ws a).length = r)
    (hlen : ∀ a ∈ E, ((ws a).map List.length).sum ≤ N)
    (hentry : ∀ a ∈ E, ∀ w ∈ ws a, ∀ h ∈ w, h ≤ B) :
    ∃ v : List (List ℕ), ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
      E.card ≤ ((N + r + 1) * (max N B + 1) ^ (N + r)) * S.card ∧
      ∀ a ∈ S, ws a = v := by
  have hlength (a : ℕ) (ha : a ∈ E) : (encodeCellGroups (ws a)).length ≤ N + r := by
    rw [encodeCellGroups_length, hr a ha]
    exact Nat.add_le_add_right (hlen a ha) r
  have hbound (a : ℕ) (ha : a ∈ E) :
      ∀ h ∈ encodeCellGroups (ws a), h ≤ max N B := by
    apply encodeCellGroups_entries
    · intro w hw
      apply le_trans _ (hlen a ha)
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) w.length (List.mem_map.mpr ⟨w, hw, rfl⟩)
    · exact hentry a ha
  obtain ⟨code, S, hSE, hcard, hsame⟩ := common_cell_list E (N + r) (max N B)
    (fun a => encodeCellGroups (ws a)) hlength hbound
  have hS : S.Nonempty := by
    by_contra hn
    have hz : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    rw [hz, Nat.mul_zero] at hcard
    exact (Nat.not_le_of_gt hE.card_pos) hcard
  obtain ⟨a₀, ha₀⟩ := hS
  refine ⟨ws a₀, S, hSE, ⟨a₀, ha₀⟩, hcard, ?_⟩
  intro a ha
  exact encodeCellGroups_injective_of_length ((hr a (hSE ha)).trans (hr a₀ (hSE ha₀)).symm)
    ((hsame a ha).trans (hsame a₀ ha₀).symm)

end Ostmann

end OAI

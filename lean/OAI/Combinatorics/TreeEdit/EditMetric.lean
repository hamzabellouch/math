import OAI.Combinatorics.TreeEdit.Model

namespace OAI

namespace TreeEdit

universe u v

namespace EditStep

variable {α : Type u} {x y : List α}

protected theorem symm (h : EditStep x y) : EditStep y x := by
  cases h with
  | insert p q a => exact .delete p q a
  | delete p q a => exact .insert p q a
  | substitute p q a b => exact .substitute p q b a

protected theorem append_left (h : EditStep x y) (p : List α) :
    EditStep (p ++ x) (p ++ y) := by
  cases h with
  | insert q r a => simpa [List.append_assoc] using EditStep.insert (p ++ q) r a
  | delete q r a => simpa [List.append_assoc] using EditStep.delete (p ++ q) r a
  | substitute q r a b =>
      simpa [List.append_assoc] using EditStep.substitute (p ++ q) r a b

protected theorem append_right (h : EditStep x y) (r : List α) :
    EditStep (x ++ r) (y ++ r) := by
  cases h with
  | insert p q a => simpa [List.append_assoc] using EditStep.insert p (q ++ r) a
  | delete p q a => simpa [List.append_assoc] using EditStep.delete p (q ++ r) a
  | substitute p q a b =>
      simpa [List.append_assoc] using EditStep.substitute p (q ++ r) a b

end EditStep

namespace EditScript

variable {α : Type u} {x y z : List α} {m n : ℕ}

protected theorem trans (h : EditScript x y m) (g : EditScript y z n) :
    EditScript x z (m + n) := by
  induction h with
  | nil => simpa using g
  | cons h h' ih => simpa [Nat.add_right_comm] using EditScript.cons h (ih g)

protected theorem one (h : EditStep x y) : EditScript x y 1 :=
  .cons h (.nil y)

protected theorem symm (h : EditScript x y n) : EditScript y x n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact ih.trans (.one h.symm)

protected theorem append_left (h : EditScript x y n) (p : List α) :
    EditScript (p ++ x) (p ++ y) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left p) ih

protected theorem append_right (h : EditScript x y n) (p : List α) :
    EditScript (x ++ p) (y ++ p) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_right p) ih

protected theorem erase (x : List α) : EditScript x [] x.length := by
  induction x with
  | nil => exact .nil []
  | cons a x ih => exact .cons (.delete [] x a) ih

theorem exists_length (x y : List α) : ∃ n, EditScript x y n :=
  ⟨_, (EditScript.erase x).trans (EditScript.erase y).symm⟩

theorem zero_iff : EditScript x y 0 ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

end EditScript

variable {α : Type u} {x y z : List α}

theorem ed_script (x y : List α) : EditScript x y (ed x y) :=
  Nat.sInf_mem (EditScript.exists_length x y)

theorem ed_le_of_script {n : ℕ} (h : EditScript x y n) : ed x y ≤ n := Nat.sInf_le h

@[simp] theorem ed_self (x : List α) : ed x x = 0 :=
  Nat.eq_zero_of_le_zero (ed_le_of_script (.nil x))

@[simp] theorem ed_eq_zero_iff : ed x y = 0 ↔ x = y := by
  constructor
  · intro h
    have := ed_script x y
    rw [h] at this
    exact EditScript.zero_iff.mp this
  · rintro rfl; exact ed_self _

theorem ed_comm (x y : List α) : ed x y = ed y x := by
  apply Nat.le_antisymm
  · exact ed_le_of_script (ed_script y x).symm
  · exact ed_le_of_script (ed_script x y).symm

theorem ed_triangle (x y z : List α) : ed x z ≤ ed x y + ed y z :=
  ed_le_of_script ((ed_script x y).trans (ed_script y z))

theorem ed_append (x y x' y' : List α) :
    ed (x ++ x') (y ++ y') ≤ ed x y + ed x' y' := by
  exact ed_le_of_script
    (((ed_script x y).append_right x').trans ((ed_script x' y').append_left y))

theorem common_lengths_nonempty (x y : List α) :
    Set.Nonempty {n : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = n} :=
  ⟨0, [], List.nil_sublist _, List.nil_sublist _, rfl⟩

theorem common_lengths_bounded (x y : List α) :
    BddAbove {n : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = n} := by
  refine ⟨x.length, ?_⟩
  rintro n ⟨z, hx, _, rfl⟩
  exact hx.length_le

theorem exists_lcs (x y : List α) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = lcs x y :=
  Nat.sSup_mem (common_lengths_nonempty x y) (common_lengths_bounded x y)

theorem length_le_lcs (hx : z.Sublist x) (hy : z.Sublist y) : z.length ≤ lcs x y :=
  le_csSup (common_lengths_bounded x y) ⟨z, hx, hy, rfl⟩

theorem lcs_le_length_left (x y : List α) : lcs x y ≤ x.length := by
  obtain ⟨z, hx, _, hz⟩ := exists_lcs x y
  exact hz ▸ hx.length_le

theorem lcs_comm (x y : List α) : lcs x y = lcs y x := by
  apply congrArg sSup
  ext n
  constructor <;> rintro ⟨z, hx, hy, hz⟩ <;> exact ⟨z, hy, hx, hz⟩

theorem lcs_le_length_right (x y : List α) : lcs x y ≤ y.length := by
  rw [lcs_comm]; exact lcs_le_length_left _ _

@[simp] theorem lcs_self (x : List α) : lcs x x = x.length := by
  exact Nat.le_antisymm (lcs_le_length_left x x)
    (length_le_lcs (List.Sublist.refl x) (List.Sublist.refl x))

@[simp] theorem deficit_self (x : List α) : deficit x x = 0 := by simp [deficit]

theorem deficit_pos_of_ne (h : x.length = y.length) (hne : x ≠ y) :
    1 ≤ deficit x y := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  have hl := hx.length_le
  have hn : z.length ≠ x.length := by
    intro hh
    exact hne ((hx.eq_of_length hh).symm.trans (hy.eq_of_length (hh.trans h)))
  simp only [deficit]
  omega

theorem sublist_erase_one {a : α} {p q z : List α} (h : z.Sublist (p ++ a :: q)) :
    ∃ z' : List α, z'.Sublist z ∧ z'.Sublist (p ++ q) ∧ z.length ≤ z'.length + 1 := by
  obtain ⟨z₁, z₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
  rcases List.sublist_cons_iff.mp h₂ with h₂ | ⟨r, rfl, hr⟩
  · exact ⟨z₁ ++ z₂, List.Sublist.refl _, h₁.append h₂, Nat.le_succ _⟩
  · refine ⟨z₁ ++ r, (List.Sublist.refl z₁).append ((List.Sublist.refl r).cons a),
      h₁.append hr, ?_⟩
    simp only [List.length_append, List.length_cons]
    omega

theorem lcs_step_loss (z : List α) (h : EditStep x y) : lcs z x ≤ lcs z y + 1 := by
  obtain ⟨s, hz, hx, hs⟩ := exists_lcs z x
  cases h with
  | insert p q a =>
      have hxy : (p ++ q).Sublist (p ++ a :: q) :=
        (List.Sublist.refl p).append ((List.Sublist.refl q).cons a)
      have hh := length_le_lcs hz (hx.trans hxy)
      omega
  | delete p q a =>
      obtain ⟨s', hss, hp, hh⟩ := sublist_erase_one hx
      have := length_le_lcs (hss.trans hz) hp
      omega
  | substitute p q a b =>
      obtain ⟨s', hss, hp, hh⟩ := sublist_erase_one hx
      have hpq : (p ++ q).Sublist (p ++ b :: q) :=
        (List.Sublist.refl p).append ((List.Sublist.refl q).cons b)
      have := length_le_lcs (hss.trans hz) (hp.trans hpq)
      omega

theorem lcs_script_loss (z : List α) {n : ℕ} (h : EditScript x y n) :
    lcs z x ≤ lcs z y + n := by
  induction h with
  | nil => simp
  | cons h _ ih => have hh := lcs_step_loss z h; omega

theorem deficit_le_ed (x y : List α) : deficit x y ≤ ed x y := by
  have h := lcs_script_loss x (ed_script x y)
  simp only [lcs_self] at h
  dsimp [deficit]
  omega

theorem sublist_script (h : z.Sublist x) : EditScript x z (x.length - z.length) := by
  induction h with
  | slnil => exact .nil []
  | @cons l₁ l₂ a h ih =>
      have hl := h.length_le
      have he : (a :: l₂).length - l₁.length = (l₂.length - l₁.length) + 1 := by
        simp only [List.length_cons]; omega
      rw [he]
      exact .cons (.delete [] l₂ a) ih
  | cons_cons a h ih =>
      simpa using ih.append_left [a]

theorem ed_le_deficits (x y : List α) :
    ed x y ≤ (x.length - lcs x y) + (y.length - lcs x y) := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  simpa [hz] using ed_le_of_script ((sublist_script hx).trans (sublist_script hy).symm)

theorem ed_le_twice_deficit (h : x.length = y.length) : ed x y ≤ 2 * deficit x y := by
  have := ed_le_deficits x y
  dsimp [deficit]
  omega

theorem length_encode {P : ℕ} {β : Type v} (c : α → Word β P) (x : List α) :
    (encode c x).length = x.length * P := by
  induction x with
  | nil => simp [encode]
  | cons a x ih =>
      change ((c a).val ++ encode c x).length = (x.length + 1) * P
      rw [List.length_append, (c a).property, ih]
      ring

theorem substitution_script (h : x.length = y.length) : EditScript x y x.length := by
  induction x generalizing y with
  | nil =>
      have : y = [] := List.length_eq_zero_iff.mp h.symm
      subst y; exact .nil []
  | cons a x ih =>
      cases y with
      | nil => simp at h
      | cons b y =>
          have hh : x.length = y.length := by simpa using h
          exact .cons (.substitute [] x a b) (by simpa using (ih hh).append_left [b])

@[simp] theorem encode_append {P : ℕ} {β : Type v} (c : α → Word β P) (x y : List α) :
    encode c (x ++ y) = encode c x ++ encode c y := by simp [encode]

@[simp] theorem encode_cons {P : ℕ} {β : Type v} (c : α → Word β P) (a : α) (x : List α) :
    encode c (a :: x) = (c a).val ++ encode c x := by simp [encode]

theorem encode_step {P : ℕ} {β : Type v} (c : α → Word β P) (h : EditStep x y) :
    EditScript (encode c x) (encode c y) P := by
  cases h with
  | insert p q a =>
      simpa [List.append_assoc, (c a).property] using
        (((EditScript.erase (c a).val).symm.append_right (encode c q)).append_left (encode c p))
  | delete p q a =>
      simpa [List.append_assoc, (c a).property] using
        (((EditScript.erase (c a).val).append_right (encode c q)).append_left (encode c p))
  | substitute p q a b =>
      have hh := substitution_script ((c a).property.trans (c b).property.symm)
      simpa [List.append_assoc, (c a).property] using
        ((hh.append_right (encode c q)).append_left (encode c p))

theorem encode_script {P n : ℕ} {β : Type v} (c : α → Word β P) (h : EditScript x y n) :
    EditScript (encode c x) (encode c y) (P * n) := by
  induction h with
  | nil => simpa using EditScript.nil (encode c _)
  | cons h _ ih =>
      simpa [Nat.mul_add, Nat.add_comm] using (encode_step c h).trans ih

theorem ed_encode_le {P : ℕ} {β : Type v} (c : α → Word β P) (x y : List α) :
    ed (encode c x) (encode c y) ≤ P * ed x y :=
  ed_le_of_script (encode_script c (ed_script x y))

end TreeEdit

end OAI

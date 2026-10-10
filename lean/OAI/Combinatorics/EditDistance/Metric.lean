import OAI.Combinatorics.EditDistance.Model
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Unrestricted edit scripts, metric inequalities, and common subsequences
-/

namespace EditDistortion

universe u v
noncomputable def indel {Alpha : Type u} (x y : List Alpha) : ℕ :=
  sInf {n | Script false n x y}

variable {Alpha : Type u} {Beta : Type v} {s : Bool}

namespace Step

theorem symm {x y : List Alpha} (h : Step s x y) : Step s y x := by
  cases h with
  | insert p q a => exact .delete p q a
  | delete p q a => exact .insert p q a
  | substitute hs p q a b => exact .substitute hs p q b a

theorem map (f : Alpha → Beta) {x y : List Alpha} (h : Step s x y) :
    Step s (x.map f) (y.map f) := by
  cases h with
  | insert p q a => simpa using Step.insert (substitutions := s) (p.map f) (q.map f) (f a)
  | delete p q a => simpa using Step.delete (substitutions := s) (p.map f) (q.map f) (f a)
  | substitute hs p q a b =>
    simpa using Step.substitute hs (p.map f) (q.map f) (f a) (f b)

theorem append_left (p : List Alpha) {x y : List Alpha} (h : Step s x y) :
    Step s (p ++ x) (p ++ y) := by
  cases h with
  | insert q r a => simpa only [List.append_assoc] using Step.insert (substitutions := s) (p ++ q) r a
  | delete q r a => simpa only [List.append_assoc] using Step.delete (substitutions := s) (p ++ q) r a
  | substitute hs q r a b =>
    simpa only [List.append_assoc] using Step.substitute hs (p ++ q) r a b

theorem append_right (q : List Alpha) {x y : List Alpha} (h : Step s x y) :
    Step s (x ++ q) (y ++ q) := by
  cases h with
  | insert p r a =>
    simpa only [List.append_assoc, List.cons_append] using
      Step.insert (substitutions := s) p (r ++ q) a
  | delete p r a =>
    simpa only [List.append_assoc, List.cons_append] using
      Step.delete (substitutions := s) p (r ++ q) a
  | substitute hs p r a b =>
    simpa only [List.append_assoc, List.cons_append] using Step.substitute hs p (r ++ q) a b

theorem length_bounds {x y : List Alpha} (h : Step s x y) :
    x.length ≤ y.length + 1 ∧ y.length ≤ x.length + 1 := by
  cases h <;> simp only [List.length_append, List.length_cons] <;> omega

theorem allow_substitution {x y : List Alpha} (h : Step false x y) : Step true x y := by
  cases h with
  | insert p q a => exact .insert p q a
  | delete p q a => exact .delete p q a
  | substitute hs => cases hs

end Step

namespace Script

theorem trans {m n : ℕ} {x y z : List Alpha}
    (h : Script s m x y) (k : Script s n y z) : Script s (m + n) x z := by
  induction h with
  | nil => simpa using k
  | @cons l x w y e h ih =>
    simpa only [Nat.add_right_comm] using Script.cons e (ih k)

theorem single {x y : List Alpha} (h : Step s x y) : Script s 1 x y :=
  .cons h (.nil y)

theorem symm {n : ℕ} {x y : List Alpha} (h : Script s n x y) : Script s n y x := by
  induction h with
  | nil x => exact .nil x
  | cons e h ih => exact ih.trans (single e.symm)

theorem map (f : Alpha → Beta) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (x.map f) (y.map f) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.map f) ih

theorem append_left (p : List Alpha) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (p ++ x) (p ++ y) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.append_left p) ih

theorem append_right (q : List Alpha) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (x ++ q) (y ++ q) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.append_right q) ih

theorem to_nil (x : List Alpha) : Script s x.length x [] := by
  induction x with
  | nil => exact .nil []
  | cons a x ih => exact .cons (.delete [] x a) ih

theorem exists_script (x y : List Alpha) : ∃ n, Script s n x y :=
  ⟨x.length + y.length, (to_nil x).trans (to_nil y).symm⟩

theorem eq_of_zero {x y : List Alpha} (h : Script s 0 x y) : x = y := by
  cases h
  rfl

theorem length_bounds {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    x.length ≤ y.length + n ∧ y.length ≤ x.length + n := by
  induction h with
  | nil x => omega
  | cons e h ih => have := e.length_bounds; omega

theorem allow_substitution {n : ℕ} {x y : List Alpha} (h : Script false n x y) :
    Script true n x y := by
  induction h with
  | nil x => exact .nil x
  | cons e h ih => exact .cons e.allow_substitution ih

end Script



theorem cost_le {n : ℕ} {x y : List Alpha} (h : Script s n x y) : cost s x y ≤ n :=
  Nat.sInf_le h

theorem cost_spec (x y : List Alpha) : Script s (cost s x y) x y :=
  Nat.sInf_mem (Script.exists_script x y)

theorem cost_refl (x : List Alpha) : cost s x x = 0 :=
  Nat.eq_zero_of_le_zero (cost_le (.nil x))

theorem cost_eq_zero_iff {x y : List Alpha} : cost s x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hc := cost_spec (s := s) x y
    rw [h] at hc
    exact hc.eq_of_zero
  · rintro rfl
    exact cost_refl _

theorem cost_symm (x y : List Alpha) : cost s x y = cost s y x := by
  apply Nat.le_antisymm
  · exact cost_le (cost_spec y x).symm
  · exact cost_le (cost_spec x y).symm

theorem cost_triangle (x y z : List Alpha) : cost s x z ≤ cost s x y + cost s y z :=
  cost_le ((cost_spec x y).trans (cost_spec y z))

theorem cost_map_le (f : Alpha → Beta) (x y : List Alpha) :
    cost s (x.map f) (y.map f) ≤ cost s x y :=
  cost_le ((cost_spec x y).map f)

theorem cost_length_bounds (x y : List Alpha) :
    x.length ≤ y.length + cost s x y ∧ y.length ≤ x.length + cost s x y :=
  (cost_spec x y).length_bounds

theorem edit_le_indel (x y : List Alpha) : edit x y ≤ indel x y :=
  cost_le ((cost_spec (s := false) x y).allow_substitution)

end EditDistortion

namespace EditDistortion

universe u v
variable {Alpha : Type u} {Beta : Type v} {s : Bool}

theorem Step.indel_simulation {x y : List Alpha} (e : Step true x y) :
    ∃ n ≤ 2, Script false n x y := by
  cases e with
  | insert p q a => exact ⟨1, by omega, Script.single (.insert p q a)⟩
  | delete p q a => exact ⟨1, by omega, Script.single (.delete p q a)⟩
  | substitute _ p q a b =>
    exact ⟨2, le_rfl, (Script.single (.delete p q a)).trans
      (Script.single (.insert p q b))⟩

theorem Script.indel_simulation {m : ℕ} {x y : List Alpha} (h : Script true m x y) :
    ∃ n ≤ 2 * m, Script false n x y := by
  induction h with
  | nil x => exact ⟨0, le_rfl, .nil x⟩
  | cons e h ih =>
    obtain ⟨n, hn, sn⟩ := ih
    obtain ⟨k, hk, sk⟩ := e.indel_simulation
    exact ⟨k + n, by omega, sk.trans sn⟩

theorem indel_le_two_edit (x y : List Alpha) : indel x y ≤ 2 * edit x y := by
  obtain ⟨n, hn, hs⟩ := (cost_spec (s := true) x y).indel_simulation
  exact (cost_le hs).trans hn

theorem Script.max_length (x y : List Alpha) : Script true (max x.length y.length) x y := by
  induction x generalizing y with
  | nil => simpa using (Script.to_nil (s := true) y).symm
  | cons a x ih =>
    cases y with
    | nil => simpa using Script.to_nil (s := true) (a :: x)
    | cons b y =>
      have hs := (ih y).append_left [b]
      have he := Step.substitute rfl [] x a b
      simpa only [List.length_cons, max_add_add_right, List.singleton_append, List.nil_append] using
        Script.cons he hs

theorem edit_le_max_length (x y : List Alpha) : edit x y ≤ max x.length y.length :=
  cost_le (Script.max_length x y)

theorem cost_map_eq_of_leftInverse (f : Alpha → Beta) (g : Beta → Alpha)
    (h : Function.LeftInverse g f) (x y : List Alpha) :
    cost s (x.map f) (y.map f) = cost s x y := by
  apply Nat.le_antisymm (cost_map_le f x y)
  have H := cost_map_le (s := s) g (x.map f) (y.map f)
  simpa only [List.map_map, h.comp_eq_id, List.map_id] using H

theorem cost_append_le (x y u v : List Alpha) :
    cost s (x ++ u) (y ++ v) ≤ cost s x y + cost s u v :=
  cost_le (((cost_spec x y).append_right u).trans ((cost_spec u v).append_left y))

theorem Script.of_sublist {x y : List Alpha} (h : x.Sublist y) :
    Script false (y.length - x.length) y x := by
  induction h with
  | slnil => exact .nil []
  | @cons x y a h ih =>
    have hl := h.length_le
    simpa only [List.length_cons, Nat.succ_sub hl, Nat.succ_eq_add_one, List.nil_append] using
      Script.cons (.delete [] y a) ih
  | @cons_cons x y a h ih =>
    simpa only [List.length_cons, Nat.add_sub_add_right, List.singleton_append] using
      ih.append_left [a]

theorem indel_le_matching_loss {x y z : List Alpha} (hx : z.Sublist x) (hy : z.Sublist y) :
    indel x y ≤ x.length + y.length - 2 * z.length := by
  have hs := (Script.of_sublist hx).trans (Script.of_sublist hy).symm
  have hx' := hx.length_le
  have hy' := hy.length_le
  have heq : x.length - z.length + (y.length - z.length) =
      x.length + y.length - 2 * z.length := by omega
  rw [heq] at hs
  exact cost_le hs

end EditDistortion

namespace EditDistortion

universe u
variable {Alpha : Type u}

theorem sublist_erase_one {z p q : List Alpha} {a : Alpha}
    (h : z.Sublist (p ++ a :: q)) :
    ∃ z' : List Alpha, z'.Sublist z ∧ z'.Sublist (p ++ q) ∧ z.length ≤ z'.length + 1 := by
  obtain ⟨z₁, z₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
  rcases List.sublist_cons_iff.mp h₂ with h₂ | ⟨r, rfl, hr⟩
  · exact ⟨z₁ ++ z₂, .refl _, h₁.append h₂, by omega⟩
  · refine ⟨z₁ ++ r, (List.Sublist.refl z₁).append ((List.Sublist.refl r).cons a),
      h₁.append hr, ?_⟩
    simp only [List.length_append, List.length_cons]
    omega

theorem Script.common_sublist {n : ℕ} {x y : List Alpha} (h : Script false n x y) :
    ∃ z : List Alpha, z.Sublist x ∧ z.Sublist y ∧ x.length + y.length ≤ n + 2 * z.length := by
  induction h with
  | nil x => exact ⟨x, .refl _, .refl _, by omega⟩
  | @cons n x v y e h ih =>
    obtain ⟨z, hzx, hzy, hz⟩ := ih
    cases e with
    | insert p q a =>
      obtain ⟨z', hz'z, hz'x, hz'L⟩ := sublist_erase_one hzx
      refine ⟨z', hz'x, hz'z.trans hzy, ?_⟩
      simp only [List.length_append, List.length_cons] at hz ⊢
      omega
    | delete p q a =>
      refine ⟨z, hzx.middle a, hzy, ?_⟩
      simp only [List.length_append, List.length_cons] at hz ⊢
      omega
    | substitute hf => cases hf

theorem indel_matching (x y : List Alpha) :
    ∃ z : List Alpha, z.Sublist x ∧ z.Sublist y ∧
      indel x y = x.length + y.length - 2 * z.length := by
  obtain ⟨z, hx, hy, hz⟩ := (cost_spec (s := false) x y).common_sublist
  refine ⟨z, hx, hy, Nat.le_antisymm (indel_le_matching_loss hx hy) ?_⟩
  change x.length + y.length - 2 * z.length ≤ cost false x y
  omega

theorem le_indel_iff {x y : List Alpha} {r : ℕ} : r ≤ indel x y ↔
    ∀ z : List Alpha, z.Sublist x → z.Sublist y → r ≤ x.length + y.length - 2 * z.length := by
  constructor
  · intro hr z hx hy
    exact hr.trans (indel_le_matching_loss hx hy)
  · intro h
    obtain ⟨z, hx, hy, hz⟩ := indel_matching x y
    rw [hz]
    exact h z hx hy

end EditDistortion

end OAI

import OAI.Combinatorics.FiniteCircle.Model

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace EditStep
variable {α β : Type*} {x y : List α}

theorem symm (h : EditStep x y) : EditStep y x := by
  cases h with
  | insert u v a => exact .delete u v a
  | delete u v a => exact .insert u v a
  | substitute u v a b => exact .substitute u v b a

theorem append_left (h : EditStep x y) (u : List α) : EditStep (u ++ x) (u ++ y) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc] using EditStep.insert (u ++ p) q a
  | delete p q a => simpa only [List.append_assoc] using EditStep.delete (u ++ p) q a
  | substitute p q a b =>
    simpa only [List.append_assoc] using EditStep.substitute (u ++ p) q a b

theorem append_right (h : EditStep x y) (v : List α) : EditStep (x ++ v) (y ++ v) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.insert p (q ++ v) a
  | delete p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.delete p (q ++ v) a
  | substitute p q a b =>
    simpa only [List.append_assoc, List.cons_append] using EditStep.substitute p (q ++ v) a b

theorem map (h : EditStep x y) (f : α → β) : EditStep (x.map f) (y.map f) := by
  cases h with
  | insert u v a => simpa using EditStep.insert (u.map f) (v.map f) (f a)
  | delete u v a => simpa using EditStep.delete (u.map f) (v.map f) (f a)
  | substitute u v a b => simpa using EditStep.substitute (u.map f) (v.map f) (f a) (f b)
end EditStep

namespace EditScript
variable {α β : Type*} {n m : ℕ} {x y z : List α}

theorem one (h : EditStep x y) : EditScript 1 x y := .cons h (.nil y)

theorem trans (h : EditScript n x y) (g : EditScript m y z) : EditScript (n + m) x z := by
  induction h with
  | nil => simpa using g
  | cons h _ ih => simpa only [Nat.add_right_comm] using EditScript.cons h (ih g)

theorem symm (h : EditScript n x y) : EditScript n y x := by
  induction h with
  | nil x => exact .nil x
  | cons h _ ih => exact ih.trans (one h.symm)

theorem append_left (h : EditScript n x y) (u : List α) : EditScript n (u ++ x) (u ++ y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left u) ih

theorem append_right (h : EditScript n x y) (v : List α) : EditScript n (x ++ v) (y ++ v) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_right v) ih

theorem map (h : EditScript n x y) (f : α → β) : EditScript n (x.map f) (y.map f) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.map f) ih

theorem deleteAll (x : List α) : EditScript x.length x [] := by
  induction x with
  | nil => exact .nil []
  | cons a x ih => exact .cons (.delete [] x a) ih

theorem insertAll (x : List α) : EditScript x.length [] x := (deleteAll x).symm

theorem exists_script (x y : List α) : ∃ n, EditScript n x y :=
  ⟨x.length + y.length, (deleteAll x).trans (insertAll y)⟩

theorem of_sublist {z x : List α} (h : z <+ x) : EditScript (x.length - z.length) x z := by
  induction h with
  | slnil => exact .nil []
  | @cons l₁ l₂ a h ih =>
    have hl := h.length_le
    simpa only [List.nil_append, List.length_cons, show l₂.length + 1 - l₁.length = l₂.length - l₁.length + 1 by omega]
      using EditScript.cons (EditStep.delete [] l₂ a) ih
  | cons_cons a h ih =>
    simpa using ih.append_left [a]

theorem of_length_eq {x y : List α} (h : x.length = y.length) : EditScript x.length x y := by
  induction x generalizing y with
  | nil =>
    have : y = [] := List.length_eq_zero_iff.mp h.symm
    subst y
    exact .nil []
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      have ht : x.length = y.length := by simpa using h
      exact .cons (.substitute [] x a b) ((ih ht).append_left [b])
end EditScript

theorem editDistance_spec {α : Type*} (x y : List α) : EditScript (editDistance x y) x y := by
  exact csInf_mem (EditScript.exists_script x y)

theorem editDistance_le_of_script {α : Type*} {x y : List α} {n : ℕ} (h : EditScript n x y) :
    editDistance x y ≤ n := csInf_le (OrderBot.bddBelow _) h

@[simp] theorem editDistance_self {α : Type*} (x : List α) : editDistance x x = 0 :=
  Nat.eq_zero_of_le_zero (editDistance_le_of_script (.nil x))

@[simp] theorem editDistance_eq_zero {α : Type*} {x y : List α} : editDistance x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hs := editDistance_spec x y
    rw [h] at hs
    cases hs
    rfl
  · rintro rfl
    exact editDistance_self x

theorem editDistance_symm {α : Type*} (x y : List α) : editDistance x y = editDistance y x := by
  apply Nat.le_antisymm
  · exact editDistance_le_of_script (editDistance_spec y x).symm
  · exact editDistance_le_of_script (editDistance_spec x y).symm

theorem editDistance_triangle {α : Type*} (x y z : List α) :
    editDistance x z ≤ editDistance x y + editDistance y z :=
  editDistance_le_of_script ((editDistance_spec x y).trans (editDistance_spec y z))

theorem editDistance_map_le {α β : Type*} (f : α → β) (x y : List α) :
    editDistance (x.map f) (y.map f) ≤ editDistance x y :=
  editDistance_le_of_script ((editDistance_spec x y).map f)

theorem editDistance_map_eq {α β : Type*} (f : α → β) (g : β → α) (hg : Function.LeftInverse g f)
    (x y : List α) : editDistance (x.map f) (y.map f) = editDistance x y := by
  apply Nat.le_antisymm (editDistance_map_le f x y)
  have hgf : ∀ a, g (f a) = a := hg
  simpa [List.map_map, Function.comp_def, hgf] using
    editDistance_map_le g (x.map f) (y.map f)

@[simp] theorem encode_nil {α : Type*} {w : ℕ} (c : α → Fin w → Bool) : encode c [] = [] := rfl
@[simp] theorem encode_cons {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (a : α) (x : List α) :
    encode c (a :: x) = List.ofFn (c a) ++ encode c x := rfl
@[simp] theorem encode_append {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x y : List α) :
    encode c (x ++ y) = encode c x ++ encode c y := List.flatMap_append
@[simp] theorem length_encode {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x : List α) :
    (encode c x).length = w * x.length := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem EditStep.encode_script {α : Type*} {w : ℕ} (c : α → Fin w → Bool) {x y : List α}
    (h : EditStep x y) : EditScript w (encode c x) (encode c y) := by
  cases h with
  | insert u v a =>
    simpa only [encode_append, encode_cons, List.length_ofFn, List.nil_append, List.append_assoc] using
      ((EditScript.insertAll (List.ofFn (c a))).append_right (encode c v)).append_left (encode c u)
  | delete u v a =>
    simpa only [encode_append, encode_cons, List.length_ofFn, List.nil_append, List.append_assoc] using
      ((EditScript.deleteAll (List.ofFn (c a))).append_right (encode c v)).append_left (encode c u)
  | substitute u v a b =>
    simpa only [encode_append, encode_cons, List.length_ofFn, List.append_assoc] using
      ((EditScript.of_length_eq (x := List.ofFn (c a)) (y := List.ofFn (c b)) (by simp)).append_right
        (encode c v)).append_left (encode c u)

theorem EditScript.encode_script {α : Type*} {w n : ℕ} (c : α → Fin w → Bool) {x y : List α}
    (h : EditScript n x y) : EditScript (w * n) (encode c x) (encode c y) := by
  induction h with
  | nil => simp only [Nat.mul_zero]; exact .nil _
  | @cons n x y z h _ ih =>
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using (h.encode_script c).trans ih

theorem editDistance_encode_le {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x y : List α) :
    editDistance (encode c x) (encode c y) ≤ w * editDistance x y :=
  editDistance_le_of_script ((editDistance_spec x y).encode_script c)

theorem lcs_exists {α : Type*} (x y : List α) :
    ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = lcs x y := by
  let s := {n : ℕ | ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = n}
  have hs : s.Nonempty := ⟨0, [], List.nil_sublist _, List.nil_sublist _, rfl⟩
  have hf : s.Finite := (Set.finite_Iic x.length).subset (by
    rintro n ⟨z, hx, _, rfl⟩
    exact hx.length_le)
  exact hs.csSup_mem hf

theorem le_lcs {α : Type*} {x y z : List α} (hx : z <+ x) (hy : z <+ y) :
    z.length ≤ lcs x y := by
  apply le_csSup
  · refine ⟨x.length, ?_⟩
    rintro n ⟨u, hu, _, rfl⟩
    exact hu.length_le
  · exact ⟨z, hx, hy, rfl⟩

theorem lcs_le_length_left {α : Type*} (x y : List α) : lcs x y ≤ x.length := by
  obtain ⟨z, hx, _, hz⟩ := lcs_exists x y
  rw [← hz]
  exact hx.length_le

theorem lcs_le_length_right {α : Type*} (x y : List α) : lcs x y ≤ y.length := by
  obtain ⟨z, _, hy, hz⟩ := lcs_exists x y
  rw [← hz]
  exact hy.length_le

theorem lcs_symm {α : Type*} (x y : List α) : lcs x y = lcs y x := by
  apply Nat.le_antisymm
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
    rw [← hz]
    exact le_lcs hy hx
  · obtain ⟨z, hy, hx, hz⟩ := lcs_exists y x
    rw [← hz]
    exact le_lcs hx hy

@[simp] theorem lcs_self {α : Type*} (x : List α) : lcs x x = x.length :=
  Nat.le_antisymm (lcs_le_length_left _ _) (le_lcs (List.Sublist.refl _) (List.Sublist.refl _))

@[simp] theorem lcs_nil_left {α : Type*} (x : List α) : lcs [] x = 0 :=
  Nat.eq_zero_of_le_zero (lcs_le_length_left _ _)

@[simp] theorem lcs_nil_right {α : Type*} (x : List α) : lcs x [] = 0 :=
  Nat.eq_zero_of_le_zero (lcs_le_length_right _ _)

theorem lcs_mono {α : Type*} {x y x' y' : List α} (hx : x <+ x') (hy : y <+ y') :
    lcs x y ≤ lcs x' y' := by
  obtain ⟨z, hz, hw, heq⟩ := lcs_exists x y
  rw [← heq]
  exact le_lcs (hz.trans hx) (hw.trans hy)

theorem lcs_encode_ge {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x y : List α) :
    w * lcs x y ≤ lcs (encode c x) (encode c y) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  rw [← hz]
  have he :=
    le_lcs (hx.flatMap (fun a => List.ofFn (c a))) (hy.flatMap (fun a => List.ofFn (c a)))
  change (encode c z).length ≤ lcs (encode c x) (encode c y) at he
  simpa only [length_encode] using he

theorem deficit_encode_le {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x y : List α) :
    deficit (encode c x) (encode c y) ≤ w * deficit x y := by
  simp only [deficit, length_encode]
  calc
    w * x.length - lcs (encode c x) (encode c y) ≤ w * x.length - w * lcs x y :=
      Nat.sub_le_sub_left (lcs_encode_ge c x y) _
    _ = w * (x.length - lcs x y) := (Nat.mul_sub _ _ _).symm

theorem sublist_common_large {α : Type*} {x y z : List α} (hx : x <+ z) (hy : y <+ z) :
    ∃ u : List α, u <+ x ∧ u <+ y ∧ x.length + y.length ≤ u.length + z.length := by
  induction z generalizing x y with
  | nil =>
    have : x = [] := List.sublist_nil.mp hx
    have : y = [] := List.sublist_nil.mp hy
    subst x; subst y
    exact ⟨[], .slnil, .slnil, le_rfl⟩
  | cons a z ih =>
    cases hx with
    | cons _ hx =>
      cases hy with
      | cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux, huy, by simp only [List.length_cons]; omega⟩
      | cons_cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux, huy.cons a, by simp only [List.length_cons]; omega⟩
    | cons_cons _ hx =>
      cases hy with
      | cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux.cons a, huy, by simp only [List.length_cons]; omega⟩
      | cons_cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨a :: u, hux.cons_cons a, huy.cons_cons a, by simp only [List.length_cons]; omega⟩

theorem lcs_triangle {α : Type*} (x y z : List α) : lcs x y + lcs y z ≤ y.length + lcs x z := by
  obtain ⟨a, hax, hay, ha⟩ := lcs_exists x y
  obtain ⟨b, hby, hbz, hb⟩ := lcs_exists y z
  obtain ⟨u, hua, hub, hlen⟩ := sublist_common_large hay hby
  have hle := le_lcs (hua.trans hax) (hub.trans hbz)
  omega

theorem unequalDeficit_triangle {α : Type*} (x y z : List α) :
    unequalDeficit x z ≤ unequalDeficit x y + unequalDeficit y z := by
  have hxy := lcs_le_length_left x y
  have hyx := lcs_le_length_right x y
  have hyz := lcs_le_length_left y z
  have hzy := lcs_le_length_right y z
  have hxz := lcs_le_length_left x z
  have hzx := lcs_le_length_right x z
  have ht := lcs_triangle x y z
  simp only [unequalDeficit]
  omega

@[simp] theorem unequalDeficit_self {α : Type*} (x : List α) : unequalDeficit x x = 0 := by
  simp [unequalDeficit]

theorem EditStep.unequalDeficit_le {α : Type*} {x y : List α} (h : EditStep x y) :
    unequalDeficit x y ≤ 1 := by
  cases h with
  | insert u v a =>
    have hs : u ++ v <+ u ++ a :: v := (List.Sublist.refl v).cons a |>.append_left u
    have hl := le_lcs (List.Sublist.refl (u ++ v)) hs
    simp only [unequalDeficit, List.length_append, List.length_cons]
    simp only [List.length_append] at hl
    omega
  | delete u v a =>
    have hs : u ++ v <+ u ++ a :: v := (List.Sublist.refl v).cons a |>.append_left u
    have hl := le_lcs hs (List.Sublist.refl (u ++ v))
    simp only [unequalDeficit, List.length_append, List.length_cons]
    simp only [List.length_append] at hl
    omega
  | substitute u v a b =>
    have ha : u ++ v <+ u ++ a :: v := (List.Sublist.refl v).cons a |>.append_left u
    have hb : u ++ v <+ u ++ b :: v := (List.Sublist.refl v).cons b |>.append_left u
    have hl := le_lcs ha hb
    simp only [unequalDeficit, List.length_append, List.length_cons]
    simp only [List.length_append] at hl
    omega

theorem EditScript.unequalDeficit_le {α : Type*} {n : ℕ} {x y : List α} (h : EditScript n x y) :
    unequalDeficit x y ≤ n := by
  induction h with
  | nil => simp
  | cons h hs ih =>
    exact (unequalDeficit_triangle _ _ _).trans ((Nat.add_le_add h.unequalDeficit_le ih).trans_eq (Nat.add_comm _ _))

theorem unequalDeficit_le_editDistance {α : Type*} (x y : List α) :
    unequalDeficit x y ≤ editDistance x y := (editDistance_spec x y).unequalDeficit_le

theorem editDistance_le_two_unequalDeficit {α : Type*} (x y : List α) :
    editDistance x y ≤ 2 * unequalDeficit x y := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  have hscript := (EditScript.of_sublist hx).trans (EditScript.of_sublist hy).symm
  have hlenx := hx.length_le
  have hleny := hy.length_le
  exact (editDistance_le_of_script hscript).trans (by simp only [unequalDeficit]; omega)

theorem deficit_eq_unequalDeficit {α : Type*} {x y : List α} (h : x.length = y.length) :
    deficit x y = unequalDeficit x y := by simp [deficit, unequalDeficit, h]

theorem deficit_le_editDistance {α : Type*} {x y : List α} (h : x.length = y.length) :
    deficit x y ≤ editDistance x y := by
  rw [deficit_eq_unequalDeficit h]
  exact unequalDeficit_le_editDistance x y

theorem editDistance_le_two_deficit {α : Type*} {x y : List α} (h : x.length = y.length) :
    editDistance x y ≤ 2 * deficit x y := by
  rw [deficit_eq_unequalDeficit h]
  exact editDistance_le_two_unequalDeficit x y

theorem lcs_cons_right_le {α : Type*} (x y : List α) (a : α) :
    lcs x (a :: y) ≤ lcs x y + 1 := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x (a :: y)
  cases hy with
  | cons _ hy => have h := le_lcs hx hy; omega
  | cons_cons _ hy =>
    have h := le_lcs ((List.Sublist.refl _).cons _ |>.trans hx) hy
    simp only [List.length_cons] at hz
    omega

@[simp] theorem lcs_cons_cons {α : Type*} (x y : List α) (a : α) :
    lcs (a :: x) (a :: y) = lcs x y + 1 := by
  apply Nat.le_antisymm
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists (a :: x) (a :: y)
    cases hx with
    | cons _ hx =>
      have h := (le_lcs hx hy).trans (lcs_cons_right_le x y a)
      omega
    | cons_cons _ hx =>
      cases hy with
      | cons _ hy =>
        have h := le_lcs hx ((List.Sublist.refl _).cons _ |>.trans hy)
        simp only [List.length_cons] at hz
        omega
      | cons_cons _ hy =>
        have h := le_lcs hx hy
        simp only [List.length_cons] at hz
        omega
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
    have h := le_lcs (hx.cons_cons a) (hy.cons_cons a)
    simp only [List.length_cons, hz] at h
    exact h

theorem lcs_reverse {α : Type*} (x y : List α) : lcs x.reverse y.reverse = lcs x y := by
  apply Nat.le_antisymm
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists x.reverse y.reverse
    have h := le_lcs hx.reverse hy.reverse
    simpa only [List.reverse_reverse, List.length_reverse, hz] using h
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
    have h := le_lcs hx.reverse hy.reverse
    simpa only [List.length_reverse, hz] using h

theorem lcs_append_common_left {α : Type*} (z x y : List α) :
    lcs (z ++ x) (z ++ y) = z.length + lcs x y := by
  induction z with
  | nil => simp
  | cons a z ih => simp only [List.cons_append, lcs_cons_cons, List.length_cons, ih]; omega

theorem lcs_append_common_right {α : Type*} (x y z : List α) :
    lcs (x ++ z) (y ++ z) = lcs x y + z.length := by
  rw [← lcs_reverse (x ++ z) (y ++ z)]
  simp only [List.reverse_append, lcs_append_common_left, lcs_reverse, List.length_reverse]
  omega

theorem deficit_append_common_right {α : Type*} (x y z : List α) :
    deficit (x ++ z) (y ++ z) = deficit x y := by
  simp only [deficit, List.length_append, lcs_append_common_right]
  omega

theorem lcs_map_ge {α β : Type*} (f : α → β) (x y : List α) :
    lcs x y ≤ lcs (x.map f) (y.map f) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  have h := le_lcs (hx.map f) (hy.map f)
  simpa only [List.length_map, hz] using h

theorem lcs_map_eq {α β : Type*} (f : α → β) (hf : Function.Injective f) (x y : List α) :
    lcs (x.map f) (y.map f) = lcs x y := by
  apply Nat.le_antisymm _ (lcs_map_ge f x y)
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists (x.map f) (y.map f)
  obtain ⟨u, hux, hu⟩ := List.sublist_map_iff.mp hx
  obtain ⟨v, hvy, hv⟩ := List.sublist_map_iff.mp hy
  have huv : u = v := List.map_injective_iff.mpr hf (hu.symm.trans hv)
  subst v
  have h := le_lcs hux hvy
  rw [← hz, hu, List.length_map]
  exact h

theorem lcs_append_replicate {α : Type*} [DecidableEq α] (x y : List α) (b : α)
    (hx : b ∉ x) (hy : b ∉ y) (n m : ℕ) :
    lcs (x ++ List.replicate n b) (y ++ List.replicate m b) = lcs x y + min n m := by
  let p : α → Bool := fun a => decide (a ≠ b)
  have hp (l : List α) (h : b ∉ l) : l.filter p = l := by
    apply List.filter_eq_self.mpr
    intro a ha
    exact decide_eq_true (by rintro rfl; exact h ha)
  have hnp (l : List α) (h : b ∉ l) : l.filter (fun a => !p a) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hab : a ≠ b := by rintro rfl; exact h ha
    simp [p, hab]
  have hpb : p b = false := by simp [p]
  have hnpb : (!p b) = true := by simp [hpb]
  apply Nat.le_antisymm
  · obtain ⟨z, hzx, hzy, hz⟩ := lcs_exists (x ++ List.replicate n b) (y ++ List.replicate m b)
    have hxt : z.filter p <+ x := by
      simpa only [List.filter_append, hp x hx, List.filter_replicate, hpb, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hzx.filter p
    have hyt : z.filter p <+ y := by
      simpa only [List.filter_append, hp y hy, List.filter_replicate, hpb, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hzy.filter p
    have hxn : (z.filter (fun a => !p a)).length ≤ n := by
      have h := (hzx.filter (fun a => !p a)).length_le
      simpa only [List.filter_append, hnp x hx, List.filter_replicate, hnpb, ↓reduceIte, List.nil_append, List.length_replicate] using h
    have hyn : (z.filter (fun a => !p a)).length ≤ m := by
      have h := (hzy.filter (fun a => !p a)).length_le
      simpa only [List.filter_append, hnp y hy, List.filter_replicate, hnpb, ↓reduceIte, List.nil_append, List.length_replicate] using h
    have hl := le_lcs hxt hyt
    have hs := List.length_eq_length_filter_add (l := z) p
    omega
  · obtain ⟨z, hzx, hzy, hz⟩ := lcs_exists x y
    have hn : List.replicate (min n m) b <+ List.replicate n b :=
      (List.replicate_sublist_replicate b).mpr (min_le_left _ _)
    have hm : List.replicate (min n m) b <+ List.replicate m b :=
      (List.replicate_sublist_replicate b).mpr (min_le_right _ _)
    have h := le_lcs (hzx.append hn) (hzy.append hm)
    simpa only [List.length_append, List.length_replicate, hz] using h

def freshPad {α : Type*} (n : ℕ) (x : List α) : List (Option α) :=
  x.map some ++ List.replicate (n - x.length) none

@[simp] theorem length_freshPad {α : Type*} {n : ℕ} {x : List α} (hx : x.length ≤ n) :
    (freshPad n x).length = n := by simp [freshPad]; omega

theorem lcs_freshPad {α : Type*} (n : ℕ) (x y : List α) :
    lcs (freshPad n x) (freshPad n y) = lcs x y + (n - max x.length y.length) := by
  classical
  unfold freshPad
  rw [lcs_append_replicate _ _ none (by simp) (by simp)]
  rw [lcs_map_eq some (Option.some_injective _)]
  congr 1
  omega

theorem deficit_freshPad {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length ≤ n) (hy : y.length ≤ n) :
    deficit (freshPad n x) (freshPad n y) = unequalDeficit x y := by
  have hl := lcs_le_length_left x y
  have hr := lcs_le_length_right x y
  simp only [deficit, length_freshPad hx, lcs_freshPad, unequalDeficit]
  omega

theorem sublist_take_with_loss {α : Type*} {x y : List α} (h : x <+ y) (k : ℕ) :
    x.take (k - (y.length - x.length)) <+ y.take k := by
  induction h generalizing k with
  | slnil => simp
  | @cons x y a h ih =>
    have hl := h.length_le
    cases k with
    | zero => simp
    | succ k =>
      simpa only [List.length_cons, List.take_succ_cons,
        show k + 1 - (y.length + 1 - x.length) = k - (y.length - x.length) by omega]
        using (ih k).cons a
  | @cons_cons x y a h ih =>
    have hl := h.length_le
    cases k with
    | zero => simp
    | succ k =>
      by_cases hk : k + 1 ≤ y.length - x.length
      · have he : k + 1 - ((a :: y).length - (a :: x).length) = 0 := by
          simp only [List.length_cons]; omega
        rw [he]
        simp
      · have he : k + 1 - ((a :: y).length - (a :: x).length) =
            (k - (y.length - x.length)) + 1 := by simp only [List.length_cons]; omega
        simpa only [he, List.take_succ_cons] using (ih k).cons_cons a

theorem unequalDeficit_take_sublist_le {α : Type*} {x y : List α} (h : x <+ y) (k : ℕ) :
    unequalDeficit (x.take k) (y.take k) ≤ y.length - x.length := by
  have hs : x.take (k - (y.length - x.length)) <+ x.take k :=
    List.take_sublist_take_left (Nat.sub_le _ _)
  have hc := le_lcs hs (sublist_take_with_loss h k)
  have hl := h.length_le
  simp only [unequalDeficit, List.length_take] at *
  omega

end FiniteCircle

end OAI

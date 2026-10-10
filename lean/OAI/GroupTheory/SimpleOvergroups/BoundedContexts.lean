import Mathlib
import OAI.GroupTheory.FiniteType.ProductGroupHomology
import OAI.GroupTheory.SimpleOvergroups.BoundedForms

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m) [DecidableEq L]

def display : C.Form → List C.Letter
  | none => [.zero]
  | some (l,g,r) => l.map .pre ++ .grp g :: r.reverse.map .del

omit [DecidableEq L] in
@[simp] theorem wordCost_pres [DecidableEq L] (l : List C.XLabel) :
    C.wordCost (l.map .pre) = (l.map WithBound.cost).sum := by
  simp [wordCost,Function.comp_def,Letter.cost]

omit [DecidableEq L] in
@[simp] theorem wordCost_dels [DecidableEq L] (l : List C.XLabel) :
    C.wordCost (l.map .del) = (l.map WithBound.cost).sum := by
  simp [wordCost,Function.comp_def,Letter.cost]

omit [DecidableEq L] in
@[simp] theorem wordCost_reverse [DecidableEq L] (w : List C.Letter) :
    C.wordCost w.reverse = C.wordCost w := by simp [wordCost]

@[simp] theorem display_cost (f : C.Form) : C.wordCost (C.display f) = f.cost C := by
  cases f with
  | none => rfl
  | some p => rcases p with ⟨l,g,r⟩; simp [display,Form.cost,Letter.cost,Nat.add_assoc]

omit [DecidableEq L] in
theorem display_congr [DecidableEq L] {f f' : C.Form} (hf : f.key C = f'.key C) :
    (C.display f).map (Letter.key C) = (C.display f').map (Letter.key C) := by
  cases f with
  | none =>
    cases f' with
    | none => rfl
    | some p => simp [Form.key] at hf
  | some p =>
    cases f' with
    | none => simp [Form.key] at hf
    | some p' =>
      rcases p with ⟨l,g,r⟩
      rcases p' with ⟨l',g',r'⟩
      simp only [Form.key,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hf
      have hp : (l.map (.pre : C.XLabel → C.Letter)).map (Letter.key C) =
          (l'.map .pre).map (Letter.key C) := by
        simpa only [List.map_map,Function.comp_def,Letter.key] using
          congrArg (List.map (fun x : L => Sum.inr (Sum.inl x) : L → Sum K (Sum L (Option L)))) hf.1
      have hd : (r.reverse.map (.del : C.XLabel → C.Letter)).map (Letter.key C) =
          (r'.reverse.map .del).map (Letter.key C) := by
        have he := congrArg (fun xs : List L => xs.reverse.map
          (fun x => Sum.inr (Sum.inr (some x)) : L → Sum K (Sum L (Option L)))) hf.2.2
        simpa only [List.map_reverse,List.map_map,Function.comp_def,Letter.key] using he
      simp only [display,List.map_append,List.map_cons,Letter.key,hp,hf.2.1,hd]

@[simp] theorem step_zero (f : C.Form) : C.step .zero f = none := by cases f <;> rfl

theorem step_identity (f : C.Form) :
    (C.step (.grp C.identity) f).key C = f.key C := by
  cases f with
  | none => rfl
  | some p =>
    rcases p with ⟨l,g,r⟩
    cases l <;> simp [step,Form.key,identity,multiply,act,WithBound.key]

theorem step_multiply (g h : C.GLabel) (f : C.Form) :
    (C.step (.grp g) (C.step (.grp h) f)).key C =
      (C.step (.grp (C.multiply g h)) f).key C := by
  cases f with
  | none => rfl
  | some p =>
    rcases p with ⟨l,q,r⟩
    cases l <;> simp [step,Form.key,multiply,act,WithBound.key,mul_assoc,mul_smul]

theorem step_group_pre (g : C.GLabel) (x : C.XLabel) (f : C.Form) :
    C.step (.grp g) (C.step (.pre x) f) = C.step (.pre (C.act g x)) f := by
  cases f with
  | none => rfl
  | some p => rcases p with ⟨l,q,r⟩; rfl

theorem step_delete_pre (y x : C.XLabel) (f : C.Form) :
    C.step (.del y) (C.step (.pre x) f) = if y.key = x.key then f else none := by
  cases f with
  | none => simp
  | some p => rcases p with ⟨l,q,r⟩; rfl

theorem step_delete_group (y : C.XLabel) (g : C.GLabel) (f : C.Form)
    {d : ℕ} (hb : y.cost + g.cost + f.cost C ≤ d) (hm : 3*d ≤ m) :
    (C.step (.del y) (C.step (.grp g) f)).key C =
      (C.step (.del (C.act (C.inverse g) y)) f).key C := by
  cases f with
  | none => rfl
  | some p =>
    rcases p with ⟨l,q,r⟩
    cases l with
    | nil => simp [step,Form.key,multiply,inverse,act,WithBound.key,mul_smul]
    | cons x l =>
      have he : y.key = (C.act g x).key ↔ (C.act (C.inverse g) y).key = x.key :=
        C.inverse_action_iff_of_total g.mem y.mem x.mem
          (by simp only [Form.cost,List.map_cons,List.sum_cons] at hb; omega) hm
      simp only [step,he]

theorem display_step (a : C.Letter) (f t : C.Form) {d : ℕ}
    (hb : a.cost C + f.cost C + t.cost C ≤ d) (hm : 3*d ≤ m) :
    (C.run (C.display (C.step a f)) t).key C =
      (C.step a (C.run (C.display f) t)).key C := by
  cases f with
  | none => simp [display]
  | some p =>
    rcases p with ⟨l,g,r⟩
    cases a with
    | zero => simp [display]
    | pre x => simp only [step,display,List.map_cons,List.cons_append,run_cons]
    | grp h =>
      cases l with
      | nil =>
        simp only [step,display,List.map_nil,List.nil_append,run_cons]
        exact (C.step_multiply h g _).symm
      | cons x l =>
        simp only [step,display,List.map_cons,List.cons_append,run_cons]
        exact congrArg (Form.key C) (C.step_group_pre h x _).symm
    | del y =>
      cases l with
      | nil =>
        simp only [step,display,List.map_nil,List.nil_append,List.reverse_append,
          List.reverse_singleton,List.map_cons,List.map_nil,
          List.singleton_append,run_cons]
        apply (C.step_identity (C.step (.del (C.act (C.inverse g) y))
          (C.run (r.reverse.map .del) t))).trans
        symm
        apply C.step_delete_group y g _ (hm := hm)
        have hc := C.run_cost (r.reverse.map Letter.del) t
        have hr : C.wordCost (r.reverse.map Letter.del) = (r.map WithBound.cost).sum := by
          rw [wordCost_dels,List.map_reverse,List.sum_reverse]
        rw [hr] at hc
        change y.cost + (0+g.cost+(r.map WithBound.cost).sum) + t.cost C ≤ d at hb
        omega
      | cons x l =>
        simp only [step]
        by_cases h : y.key = x.key
        · rw [ite_eq_left h]
          simp only [display,List.map_cons,List.cons_append,run_cons]
          exact congrArg (Form.key C) ((C.step_delete_pre y x _).trans (ite_eq_left h)).symm
        · rw [ite_eq_right h]
          simp only [display,List.map_cons,List.cons_append,run_cons,run_nil,step_zero]
          exact congrArg (Form.key C) ((C.step_delete_pre y x _).trans (ite_eq_right h)).symm

theorem run_display_normalize (w : List C.Letter) (t : C.Form) {d : ℕ}
    (hb : C.wordCost w + t.cost C ≤ d) (hm : 3*d ≤ m) :
    (C.run w t).key C = (C.run (C.display (C.normalize w)) t).key C := by
  induction w with
  | nil =>
    simpa only [normalize,run_nil,display,List.map_nil,List.reverse_nil,List.nil_append,
      run_cons] using (C.step_identity t).symm
  | cons a w ih =>
    have hc := C.normalize_cost w
    have ht : C.wordCost w + t.cost C ≤ d := by simp only [wordCost_cons] at hb; omega
    have he := C.step_congr (a := a) rfl (ih ht)
      (hb := by have := C.run_cost w t; simp only [wordCost_cons] at hb; omega)
      (hb' := by
        have hh := C.run_cost (C.display (C.normalize w)) t
        rw [display_cost] at hh
        simp only [wordCost_cons] at hb
        omega)
    rw [run_cons]
    exact he.trans (C.display_step a (C.normalize w) t
      (by simp only [wordCost_cons] at hb; omega) hm).symm

theorem normalize_right_context {u v b : List C.Letter} {d : ℕ}
    (he : (C.normalize u).key C = (C.normalize v).key C)
    (hu : C.wordCost (u++b) ≤ d) (hv : C.wordCost (v++b) ≤ d) (hm : 3*d ≤ m) :
    (C.normalize (u++b)).key C = (C.normalize (v++b)).key C := by
  have hb := C.normalize_cost b
  have huc := C.normalize_cost u
  have hvc := C.normalize_cost v
  simp only [wordCost_append] at hu hv
  change (C.run (u++b) _).key C = (C.run (v++b) _).key C
  rw [run_append,run_append]
  change (C.run u (C.normalize b)).key C = (C.run v (C.normalize b)).key C
  rw [C.run_display_normalize u (C.normalize b) (by omega) hm,
    C.run_display_normalize v (C.normalize b) (by omega) hm]
  apply C.run_congr (C.display_congr he) rfl
  · rw [display_cost]; omega
  · rw [display_cost]; omega

theorem normalize_context {u v a b : List C.Letter} {d : ℕ}
    (he : (C.normalize u).key C = (C.normalize v).key C)
    (hu : C.wordCost (a++u++b) ≤ d) (hv : C.wordCost (a++v++b) ≤ d) (hm : 3*d ≤ m) :
    (C.normalize (a++u++b)).key C = (C.normalize (a++v++b)).key C := by
  simp only [wordCost_append] at hu hv
  rw [List.append_assoc,List.append_assoc]
  apply C.normalize_left_context (C.normalize_right_context he
    (by simp only [wordCost_append]; omega) (by simp only [wordCost_append]; omega) hm)
  · simp only [wordCost_append]; omega
  · simp only [wordCost_append]; omega

theorem normalize_zero_context {u a b : List C.Letter} {d : ℕ}
    (he : (C.normalize u).key C = none)
    (hu : C.wordCost (a++u++b) ≤ d) (hm : 3*d ≤ m) :
    (C.normalize (a++u++b)).key C = none := by
  have hz : (C.normalize [.zero]).key C = none := rfl
  have hh := C.normalize_context (he.trans hz.symm) hu
    (show C.wordCost (a++[.zero]++b) ≤ d from by
      simp only [wordCost_append,wordCost_cons,wordCost_nil,Letter.cost] at hu ⊢
      omega) hm
  simpa only [normalize,run_append,run_cons,step_zero,run_none,Form.key,
    Option.map_none] using hh

theorem normalize_nil_ne_zero : (C.normalize []).key C ≠ none := by
  simp only [normalize,run_nil,Form.key,Option.map_some,ne_eq,reduceCtorEq,not_false_eq_true]

end SimpleFInftyOvergroups.BoundedEncoding.ActionCalculus

end OAI

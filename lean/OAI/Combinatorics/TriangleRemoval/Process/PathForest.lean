import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def PathForest (s : ℕ) :=
  {p : Fin s → Option (Fin s) // ∀ i j, p i = some j → j < i}

namespace PathForest
variable {s : ℕ}

noncomputable instance : Fintype (PathForest s) := by
  classical
  unfold PathForest
  infer_instance
noncomputable instance : DecidableEq (PathForest s) := Classical.decEq _

def parent (F : PathForest s) : Fin s → Option (Fin s) := F.val

def Step (F : PathForest s) (x y : Fin s) : Prop := F.parent y = some x

def Ancestor (F : PathForest s) : Fin s → Fin s → Prop := Relation.ReflTransGen F.Step

def OnPath (F : PathForest s) (a : Option (Fin s)) (v : Fin s) : Prop :=
  ∃ w, a = some w ∧ F.Ancestor v w

lemma step_lt (F : PathForest s) {x y : Fin s} (h : F.Step x y) : x < y := F.property y x h

lemma ancestor_le (F : PathForest s) {x y : Fin s} (h : F.Ancestor x y) : x ≤ y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hp ih => exact ih.trans (F.step_lt hp).le

lemma predecessor_unique (F : PathForest s) {x y z : Fin s}
    (hx : F.Step x z) (hy : F.Step y z) : x = y := Option.some.inj (hx.symm.trans hy)

lemma ancestor_eq_or_predecessor (F : PathForest s) {x z : Fin s}
    (h : F.Ancestor x z) : x = z ∨ ∃ y, F.Step y z ∧ F.Ancestor x y := by
  cases h with
  | refl => exact Or.inl rfl
  | @tail y z hxy hyz => exact Or.inr ⟨y,hyz,hxy⟩

lemma ancestors_comparable (F : PathForest s) {x y z : Fin s}
    (hx : F.Ancestor x z) (hy : F.Ancestor y z) :
    F.Ancestor x y ∨ F.Ancestor y x := by
  induction hx generalizing y with
  | refl => exact Or.inr hy
  | @tail v z hxv hvz ih =>
    rcases F.ancestor_eq_or_predecessor hy with rfl | ⟨w,hwz,hyw⟩
    · exact Or.inl (Relation.ReflTransGen.tail hxv hvz)
    · have he := F.predecessor_unique hvz hwz
      subst w
      exact ih hyw

lemma onPath_ancestor (F : PathForest s) {a : Option (Fin s)} {x y : Fin s}
    (hx : F.Ancestor x y) (hy : F.OnPath a y) : F.OnPath a x := by
  obtain ⟨w,rfl,hyw⟩ := hy
  exact ⟨w,rfl,hx.trans hyw⟩

lemma onPath_comparable (F : PathForest s) {a : Option (Fin s)} {x y : Fin s}
    (hx : F.OnPath a x) (hy : F.OnPath a y) : F.Ancestor x y ∨ F.Ancestor y x := by
  obtain ⟨u,hu,hxu⟩ := hx
  obtain ⟨v,hv,hyv⟩ := hy
  have he := Option.some.inj (hu.symm.trans hv)
  subst v
  exact F.ancestors_comparable hxu hyv

lemma onPath_before (F : PathForest s) {a : Option (Fin s)} {x y : Fin s}
    (hx : F.OnPath a x) (hy : F.OnPath a y) (hxy : x < y) : F.Ancestor x y := by
  rcases F.onPath_comparable hx hy with h | h
  · exact h
  · exact False.elim (not_le_of_gt hxy (F.ancestor_le h))

theorem parent_determined (F H : PathForest s) (a b : Option (Fin s))
    (hcover : ∀ v, F.OnPath a v ∨ F.OnPath b v)
    (ha : ∀ v, F.OnPath a v ↔ H.OnPath a v)
    (hb : ∀ v, F.OnPath b v ↔ H.OnPath b v) : F = H := by
  have hone : ∀ (U W : PathForest s) (c : Option (Fin s)) (v p : Fin s),
      (∀ i, U.OnPath c i ↔ W.OnPath c i) → U.OnPath c v → U.Step p v →
      ∃ q, W.Step q v ∧ p ≤ q := by
    intro U W c v p he hv hp
    have hpc := U.onPath_ancestor (Relation.ReflTransGen.single hp) hv
    have hbefore := W.onPath_before ((he p).mp hpc) ((he v).mp hv) (U.step_lt hp)
    rcases W.ancestor_eq_or_predecessor hbefore with h | ⟨q,hq,hpq⟩
    · exact False.elim (ne_of_lt (U.step_lt hp) h)
    · exact ⟨q,hq,W.ancestor_le hpq⟩
  apply Subtype.ext
  funext v
  change F.parent v = H.parent v
  obtain ⟨c,hcv,he⟩ : ∃ c, F.OnPath c v ∧ ∀ i, F.OnPath c i ↔ H.OnPath c i := by
    rcases hcover v with hv | hv
    · exact ⟨a,hv,ha⟩
    · exact ⟨b,hv,hb⟩
  cases hF : F.parent v with
  | none =>
    cases hH : H.parent v with
    | none => rfl
    | some q =>
      obtain ⟨p,hp,_⟩ := hone H F c v q (fun i => (he i).symm) ((he v).mp hcv) hH
      change F.parent v = some p at hp
      rw [hF] at hp
      contradiction
  | some p =>
    obtain ⟨q,hq,hpq⟩ := hone F H c v p he hcv hF
    obtain ⟨p',hp',hqp'⟩ := hone H F c v q (fun i => (he i).symm) ((he v).mp hcv) hq
    have hpp' : p = p' := F.predecessor_unique hF hp'
    have hpq' : p = q := le_antisymm hpq (hpp' ▸ hqp')
    rw [show H.parent v = some q from hq,hpq']

inductive PathColor
  | left | right | both
  deriving DecidableEq

instance : Fintype PathColor where
  elems := {.left,.right,.both}
  complete := by intro x; cases x <;> simp

noncomputable def color (F : PathForest s) (a b : Option (Fin s)) (v : Fin s) : PathColor := by
  classical
  exact if F.OnPath a v then if F.OnPath b v then .both else .left else .right

lemma color_left_iff (F : PathForest s) (a b : Option (Fin s)) (v : Fin s) :
    F.color a b v ≠ .right ↔ F.OnPath a v := by
  classical
  simp only [color]
  split_ifs <;> simp_all

lemma color_right_iff (F : PathForest s) (a b : Option (Fin s)) (v : Fin s)
    (hc : F.OnPath a v ∨ F.OnPath b v) :
    F.color a b v ≠ .left ↔ F.OnPath b v := by
  classical
  simp only [color]
  split_ifs <;> simp_all

open Classical in

theorem two_path_forest_count (a b : Option (Fin s)) :
    Fintype.card {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v} ≤ 3^s := by
  classical
  let f : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v} → (Fin s → PathColor) :=
    fun F => F.val.color a b
  have hf : Function.Injective f := by
    intro F H h
    apply Subtype.ext
    apply parent_determined F.val H.val a b F.property
    · intro v
      rw [← color_left_iff,← color_left_iff]
      exact congrArg (fun z => z ≠ PathColor.right) (congrFun h v) |>.to_iff
    · intro v
      rw [← color_right_iff _ _ _ _ (F.property v),← color_right_iff _ _ _ _ (H.property v)]
      exact congrArg (fun z => z ≠ PathColor.left) (congrFun h v) |>.to_iff
  have hh := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_fun,show Fintype.card PathColor = 3 from rfl] using hh

end PathForest
end SharpTerminalLeave

end

end OAI

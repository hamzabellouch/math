import Mathlib
import OAI.GroupTheory.PeriodicGroups.Homology.RelativeHomology

namespace OAI

section
universe u v w
namespace SourceBurnside.Palette

inductive Check (C : Type u)
  | idle
  | passed (seek : C)
  | head (seek : C)
  deriving DecidableEq

structure Cell (C : Type u) (A : Type v) where
  color : C
  check : Check C
  aux : A
  deriving DecidableEq

variable {C : Type u} {A : Type v}

variable (head : A → Prop)

inductive Pair : Check C → Check C → Prop
  | idle : Pair .idle .idle
  | passed (x : C) : Pair (.passed x) (.passed x)
  | next (x : C) : Pair (.passed x) (.head x)
  | rest (x : C) : Pair (.head x) .idle

def LastOK : Check C → Prop
  | .idle => True
  | .head _ => True
  | .passed _ => False

def Syntax (w : List (Cell C A)) : Prop :=
  List.IsChain (fun a b => Pair a.check b.check) w ∧
    ∀ c ∈ w.getLast?, LastOK c.check

def Form (w : List (Cell C A)) : Prop :=
  (∀ c ∈ w, c.check = .idle) ∨
    ∃ p c s x, w = p ++ c :: s ∧ c.check = .head x ∧
      (∀ a ∈ p, a.check = .passed x) ∧ (∀ a ∈ s, a.check = .idle)

lemma syntax_tail {c : Cell C A} {w : List (Cell C A)} (h : Syntax (c :: w)) :
    Syntax w := by
  refine ⟨h.1.tail, ?_⟩
  intro a ha
  cases w with
  | nil => simp at ha
  | cons d t => exact h.2 a (by simpa using ha)

lemma syntax_form (w : List (Cell C A)) (h : Syntax w) : Form w := by
  induction w with
  | nil => exact Or.inl (by simp)
  | cons c w ih =>
    have ht := ih (syntax_tail h)
    cases w with
    | nil =>
      have hc := h.2 c (by simp)
      cases hck : c.check with
      | idle => exact Or.inl (by simp [hck])
      | passed x => simp [LastOK, hck] at hc
      | head x => exact Or.inr ⟨[], c, [], x, by simp, hck, by simp, by simp⟩
    | cons d t =>
      have hp : Pair c.check d.check := h.1.rel
      generalize hcc : c.check = cc at hp
      generalize hdc : d.check = dc at hp
      cases hp with
      | idle =>
        rcases ht with ht | ⟨p, a, s, x, heq, ha, hpre, hs⟩
        · exact Or.inl (by simp_all)
        · cases p with
          | nil => simp only [List.nil_append, List.cons.injEq] at heq
                   obtain ⟨rfl, rfl⟩ := heq
                   simp_all
          | cons e p => simp only [List.cons_append, List.cons.injEq] at heq
                        obtain ⟨rfl, heq⟩ := heq
                        have := hpre d (by simp)
                        simp_all
      | passed x =>
        rcases ht with ht | ⟨p, a, s, y, heq, ha, hpre, hs⟩
        · have := ht d (by simp); simp_all
        · cases p with
          | nil => simp only [List.nil_append, List.cons.injEq] at heq
                   obtain ⟨rfl, rfl⟩ := heq
                   simp_all
          | cons e p =>
            simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨rfl, heq⟩ := heq
            have hxy := hpre d (by simp)
            have hxy' : x = y := by simpa [hdc] using hxy
            subst y
            exact Or.inr ⟨c :: d :: p, a, s, x,
              by simp [heq], ha, by simp_all, hs⟩
      | next x =>
        rcases ht with ht | ⟨p, a, s, y, heq, ha, hpre, hs⟩
        · have := ht d (by simp); simp_all
        · cases p with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            have hxy : x = y := by simpa [hdc] using ha
            subst y
            exact Or.inr ⟨[c], d, t, x, rfl, ha, by simp_all, hs⟩
          | cons e p =>
            simp only [List.cons_append, List.cons.injEq] at heq
            obtain ⟨rfl, heq⟩ := heq
            have := hpre d (by simp)
            simp_all
      | rest x =>
        rcases ht with ht | ⟨p, a, s, y, heq, ha, hpre, hs⟩
        · exact Or.inr ⟨[], c, d :: t, x, rfl, hcc, by simp, ht⟩
        · cases p with
          | nil => simp only [List.nil_append, List.cons.injEq] at heq
                   obtain ⟨rfl, rfl⟩ := heq
                   simp_all
          | cons e p => simp only [List.cons_append, List.cons.injEq] at heq
                        obtain ⟨rfl, heq⟩ := heq
                        have := hpre d (by simp)
                        simp_all

section Chains
variable {α : Type*} {R : α → α → Prop}

lemma chain_change_head (s : List α) (a b : α) (h : ∀ c, R a c ↔ R b c) :
    List.IsChain R (a :: s) ↔ List.IsChain R (b :: s) := by
  cases s with
  | nil => simp
  | cons c s => simp only [List.isChain_cons_cons, h c]

lemma chain_change_last (p : List α) (a b : α) (h : ∀ c, R c a ↔ R c b) :
    List.IsChain R (p ++ [a]) ↔ List.IsChain R (p ++ [b]) := by
  induction p with
  | nil => simp
  | cons c p ih =>
    cases p with
    | nil => simpa only [List.cons_append, List.nil_append, List.isChain_pair] using h c
    | cons d p =>
      simp only [List.cons_append, List.isChain_cons_cons] at ih ⊢
      exact and_congr Iff.rfl ih

lemma chain_replace_one (p s : List α) (a b : α)
    (hl : ∀ c, R c a ↔ R c b) (hr : ∀ c, R a c ↔ R b c) :
    List.IsChain R (p ++ a :: s) ↔ List.IsChain R (p ++ b :: s) := by
  exact List.isChain_split.trans ((and_congr (chain_change_last p a b hl)
    (chain_change_head s a b hr)).trans List.isChain_split.symm)

lemma chain_replace_two (p s : List α) (a b a' b' : α)
    (hl : ∀ c, R c a ↔ R c a') (hr : ∀ c, R b c ↔ R b' c)
    (hm : R a b ↔ R a' b') :
    List.IsChain R (p ++ a :: b :: s) ↔ List.IsChain R (p ++ a' :: b' :: s) := by
  rw [List.isChain_append_cons_cons, List.isChain_append_cons_cons,
    chain_change_last p a a' hl, chain_change_head s b b' hr, hm]

end Chains

def setCheck (c : Cell C A) (k : Check C) : Cell C A := { c with check := k }

@[simp] lemma setCheck_check (c : Cell C A) (k : Check C) : (setCheck c k).check = k := rfl
@[simp] lemma setCheck_color (c : Cell C A) (k : Check C) : (setCheck c k).color = c.color := rfl
@[simp] lemma setCheck_aux (c : Cell C A) (k : Check C) : (setCheck c k).aux = c.aux := rfl
@[simp] lemma setCheck_self (c : Cell C A) : setCheck c c.check = c := by cases c; rfl

lemma pair_in_head_passed (a : Check C) (x : C) :
    Pair a (.head x) ↔ Pair a (.passed x) := by
  cases a <;> constructor <;> intro h <;> cases h <;> constructor

lemma pair_out_head_idle (a : Check C) (x : C) :
    Pair (.head x) a ↔ Pair .idle a := by
  cases a <;> constructor <;> intro h <;> cases h <;> constructor

lemma syntax_create (a : Cell C A) (s : List (Cell C A)) (x : C) :
    Syntax (setCheck a .idle :: s) ↔ Syntax (setCheck a (.head x) :: s) := by
  unfold Syntax
  apply and_congr
  · exact chain_change_head s _ _ (fun c => (pair_out_head_idle c.check x).symm)
  · cases s with
    | nil => simp [LastOK]
    | cons b s => rfl

lemma syntax_walk (p s : List (Cell C A)) (a b : Cell C A) (x : C) :
    Syntax (p ++ setCheck a (.head x) :: setCheck b .idle :: s) ↔
      Syntax (p ++ setCheck a (.passed x) :: setCheck b (.head x) :: s) := by
  unfold Syntax
  apply and_congr
  · exact chain_replace_two p s _ _ _ _
      (fun c => pair_in_head_passed c.check x)
      (fun c => (pair_out_head_idle c.check x).symm)
      ⟨fun _ => Pair.next x, fun _ => Pair.rest x⟩
  · simp only [List.getLast?_append_cons, List.getLast?_cons_cons]
    cases s with
    | nil => simp [LastOK]
    | cons c s => rfl

def Safe (w : List (Cell C A)) : Prop :=
  ∀ c ∈ w, ∀ x, c.check = .passed x → c.color ≠ x

@[simp] lemma safe_nil : Safe ([] : List (Cell C A)) := by simp [Safe]
@[simp] lemma safe_append (v w : List (Cell C A)) : Safe (v ++ w) ↔ Safe v ∧ Safe w := by
  simp only [Safe, List.forall_mem_append]
@[simp] lemma safe_cons (a : Cell C A) (w : List (Cell C A)) :
    Safe (a :: w) ↔ (∀ x, a.check = .passed x → a.color ≠ x) ∧ Safe w := by
  simp [Safe]

lemma safe_create (a : Cell C A) (w : List (Cell C A)) (x : C) :
    Safe (setCheck a .idle :: w) ↔ Safe (setCheck a (.head x) :: w) := by simp

lemma safe_walk (p s : List (Cell C A)) (a b : Cell C A) (x : C)
    (h : a.color ≠ x) :
    Safe (p ++ setCheck a (.head x) :: setCheck b .idle :: s) ↔
      Safe (p ++ setCheck a (.passed x) :: setCheck b (.head x) :: s) := by simp [h]

inductive Edge (head : A → Prop) : List (Cell C A) → List (Cell C A) → Prop
  | create (a : Cell C A) (s : List (Cell C A)) (x : C) :
      Edge head (setCheck a .idle :: s) (setCheck a (.head x) :: s)
  | walk (p s : List (Cell C A)) (a b : Cell C A) (x : C) (h : a.color ≠ x) :
      Edge head (p ++ setCheck a (.head x) :: setCheck b .idle :: s)
        (p ++ setCheck a (.passed x) :: setCheck b (.head x) :: s)
  | swap (p s : List (Cell C A)) (a b : Cell C A)
      (hc : a.check = b.check) (ha : a.aux = b.aux)
      (hc' : ∀ x, a.check ≠ .head x) (ha' : ¬ head a.aux) :
      Edge head (p ++ a :: b :: s) (p ++ b :: a :: s)
  | auxiliary (v w : List (Cell C A))
      (h : List.Forall₂ (fun a b => a.color = b.color ∧ a.check = b.check) v w) :
      Edge head v w

def Step (head : A → Prop) (v w : List (Cell C A)) : Prop :=
  Edge head v w ∨ Edge head w v
abbrev Reach (head : A → Prop) := Relation.ReflTransGen (Step (C := C) head)

lemma forall₂_colors {v w : List (Cell C A)}
    (h : List.Forall₂ (fun a b => a.color = b.color ∧ a.check = b.check) v w) :
    v.map Cell.color = w.map Cell.color := by
  induction h with
  | nil => rfl
  | @cons a b v w hab h ih => simp [hab.1, ih]

lemma forall₂_checks {v w : List (Cell C A)}
    (h : List.Forall₂ (fun a b => a.color = b.color ∧ a.check = b.check) v w) :
    v.map Cell.check = w.map Cell.check := by
  induction h with
  | nil => rfl
  | @cons a b v w hab h ih => simp [hab.2, ih]

lemma syntax_of_checks {v w : List (Cell C A)} (h : v.map Cell.check = w.map Cell.check) :
    Syntax v ↔ Syntax w := by
  unfold Syntax
  have hc : List.IsChain (fun a b : Cell C A => Pair a.check b.check) v ↔
      List.IsChain (fun a b : Cell C A => Pair a.check b.check) w := by
    calc
      _ ↔ List.IsChain Pair (v.map Cell.check) := (List.isChain_map _).symm
      _ ↔ List.IsChain Pair (w.map Cell.check) := by rw [h]
      _ ↔ _ := List.isChain_map _
  apply and_congr hc
  have hl := congr_arg List.getLast? h
  rw [List.getLast?_map, List.getLast?_map] at hl
  simpa only [Option.mem_def, Option.map_eq_some_iff, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] using
    (show (∀ k ∈ v.getLast?.map Cell.check, LastOK k) ↔
      (∀ k ∈ w.getLast?.map Cell.check, LastOK k) from by rw [hl])

lemma safe_of_forall₂ {v w : List (Cell C A)}
    (h : List.Forall₂ (fun a b => a.color = b.color ∧ a.check = b.check) v w) :
    Safe v ↔ Safe w := by
  induction h with
  | nil => rfl
  | @cons a b v w hab h ih => simp only [safe_cons, hab.1, hab.2, ih]

lemma edge_safe {v w : List (Cell C A)} (h : Edge head v w) : Safe v ↔ Safe w := by
  cases h with
  | create a s x => exact safe_create a s x
  | walk p s a b x h => exact safe_walk p s a b x h
  | swap p s a b hc ha hc' ha' => simp only [safe_append, safe_cons]; tauto
  | auxiliary v w h => exact safe_of_forall₂ h

lemma edge_syntax {v w : List (Cell C A)} (h : Edge head v w) : Syntax v ↔ Syntax w := by
  cases h with
  | create a s x => exact syntax_create a s x
  | walk p s a b x h => exact syntax_walk p s a b x
  | swap p s a b hc ha hc' ha' =>
    exact syntax_of_checks (by simp [hc])
  | auxiliary v w h => exact syntax_of_checks (forall₂_checks h)

lemma edge_color_perm {v w : List (Cell C A)} (h : Edge head v w) :
    (v.map Cell.color).Perm (w.map Cell.color) := by
  cases h with
  | create a s x => simp
  | walk p s a b x h => simp
  | swap p s a b hc ha hc' ha' =>
    simp only [List.map_append, List.map_cons]
    exact (List.Perm.swap _ _ _).append_left _
  | auxiliary v w h => rw [forall₂_colors h]

def Zero (w : List (Cell C A)) : Prop :=
  (∃ a ∈ w, ∃ x, a.check = .passed x ∧ a.color = x) ∨
  (∃ p a b s, w = p ++ a :: b :: s ∧ a.color = b.color) ∨
  (∃ p a x, w = p ++ [a] ∧ a.check = .head x ∧ a.color ≠ x)

lemma prefix_passed (p : List (Cell C A)) (a : Cell C A) (x : C)
    (hc : List.IsChain (fun a b => Pair a.check b.check) (p ++ [a]))
    (ha : a.check = .passed x ∨ a.check = .head x) :
    ∀ c ∈ p, c.check = .passed x := by
  induction p with
  | nil => simp
  | cons b p ih =>
    have ht := ih hc.tail
    have hb : b.check = .passed x := by
      cases p with
      | nil =>
        have hp : Pair b.check a.check := hc.rel
        rcases ha with ha | ha <;> rw [ha] at hp
        · generalize hb : b.check = ck at hp
          cases hp
          rfl
        · generalize hb : b.check = ck at hp
          cases hp
          rfl
      | cons c t =>
        have hp : Pair b.check c.check := hc.rel
        rw [ht c (by simp)] at hp
        generalize hb : b.check = ck at hp
        cases hp
        rfl
    simpa using (show b.check = .passed x ∧ ∀ c ∈ p, c.check = .passed x from ⟨hb, ht⟩)

theorem not_zero_of_invariants {w : List (Cell C A)}
    (hsyn : Syntax w) (hsafe : Safe w) (hnd : (w.map Cell.color).Nodup)
    (hcover : ∀ x : C, x ∈ w.map Cell.color) : ¬ Zero w := by
  rintro (⟨a, ha, x, hx, hax⟩ | ⟨p, a, b, s, rfl, hab⟩ | ⟨p, a, x, rfl, hx, hax⟩)
  · exact hsafe a ha x hx hax
  · have hn : (a.color :: b.color :: s.map Cell.color).Nodup :=
      (List.nodup_append.mp (by simpa using hnd)).2.1
    exact (List.nodup_cons.mp hn).1 (by simp [hab])
  · have hp := prefix_passed p a x hsyn.1 (Or.inr hx)
    obtain ⟨b, hb, hbx⟩ := List.mem_map.mp (hcover x)
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hsafe b (List.mem_append_left _ hb) x (hp b hb) hbx
    · exact hax hbx

theorem reach_invariants {v w : List (Cell C A)} (h : Reach head v w) :
    (Syntax v ↔ Syntax w) ∧ (Safe v ↔ Safe w) ∧
      (v.map Cell.color).Perm (w.map Cell.color) := by
  induction h with
  | refl => exact ⟨Iff.rfl, Iff.rfl, .refl _⟩
  | @tail b c huv hbc ih =>
    rcases hbc with hbc | hcb
    · exact ⟨ih.1.trans (edge_syntax head hbc), ih.2.1.trans (edge_safe head hbc),
        ih.2.2.trans (edge_color_perm head hbc)⟩
    · exact ⟨ih.1.trans (edge_syntax head hcb).symm, ih.2.1.trans (edge_safe head hcb).symm,
        ih.2.2.trans (edge_color_perm head hcb).symm⟩

theorem clean_not_zero {v w : List (Cell C A)} (h : Reach head v w)
    (hsyn : Syntax v) (hi : ∀ a ∈ v, a.check = .idle)
    (hnd : (v.map Cell.color).Nodup) (hall : ∀ x, x ∈ v.map Cell.color) : ¬ Zero w := by
  have inv := reach_invariants head h
  have hv : Safe v := by
    intro a ha x hx
    rw [hi a ha] at hx
    cases hx
  exact not_zero_of_invariants (inv.1.mp hsyn) (inv.2.1.mp hv)
    (inv.2.2.nodup_iff.mp hnd) (fun x => (inv.2.2.mem_iff).mp (hall x))

def idle (w : List (Cell C A)) : List (Cell C A) := w.map (fun c => setCheck c .idle)

@[simp] lemma idle_append (v w : List (Cell C A)) : idle (v ++ w) = idle v ++ idle w :=
  List.map_append
@[simp] lemma idle_cons (a : Cell C A) (w : List (Cell C A)) :
    idle (a :: w) = setCheck a .idle :: idle w := rfl
@[simp] lemma idle_setCheck (a : Cell C A) (x : Check C) :
    setCheck (setCheck a x) .idle = setCheck a .idle := rfl

lemma idle_eq {w : List (Cell C A)} (h : ∀ a ∈ w, a.check = .idle) : idle w = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha := h a (by simp)
    have hw := ih (fun b hb => h b (by simp [hb]))
    rw [idle_cons, hw, ← ha, setCheck_self]

lemma rollback_head (p : List (Cell C A)) (a : Cell C A) (s : List (Cell C A)) (x : C)
    (hp : ∀ c ∈ p, c.check = .passed x)
    (hn : ∀ c ∈ p, c.color ≠ x) (hs : ∀ c ∈ s, c.check = .idle) :
    Reach head (p ++ setCheck a (.head x) :: s) (idle (p ++ a :: s)) := by
  induction p using List.reverseRecOn generalizing a s with
  | nil =>
    have eqs := idle_eq hs
    have st : Step head (setCheck a (.head x) :: s) (setCheck a .idle :: s) :=
      Or.inr (Edge.create a s x)
    simpa only [List.nil_append, idle_cons, eqs] using
      (Relation.ReflTransGen.single st)
  | append_singleton p b ih =>
    have hb := hp b (by simp)
    have hb' := hn b (by simp)
    have hbp : setCheck b (.passed x) = b := by rw [← hb]; exact setCheck_self b
    have step : Step head (p ++ b :: setCheck a (.head x) :: s)
        (p ++ setCheck b (.head x) :: setCheck a .idle :: s) := by
      apply Or.inr
      simpa only [hbp] using Edge.walk (head := head) p s b a x hb'
    have rest := ih b (setCheck a .idle :: s)
      (fun c hc => hp c (List.mem_append_left _ hc))
      (fun c hc => hn c (List.mem_append_left _ hc)) (by simp only [List.forall_mem_cons, setCheck_check]; exact ⟨True.intro, hs⟩)
    have hd : idle (p ++ b :: setCheck a .idle :: s) = idle ((p ++ [b]) ++ a :: s) := by
      simp [idle, List.append_assoc]
    rw [hd] at rest
    simpa only [List.append_assoc, List.singleton_append] using
      (Relation.ReflTransGen.head step rest)

theorem rollback {w : List (Cell C A)} (hs : Syntax w) :
    Zero w ∨ Reach head w (idle w) := by
  classical
  by_cases hsafe : Safe w
  · rcases syntax_form w hs with hi | ⟨p, a, s, x, rfl, ha, hp, hs⟩
    · apply Or.inr
      rw [idle_eq hi]
    · have hea : setCheck a (.head x) = a := by rw [← ha]; exact setCheck_self a
      have hr := rollback_head head p a s x hp
        (fun c hc => hsafe c (List.mem_append_left _ hc) x (hp c hc)) hs
      exact Or.inr (by simpa only [hea] using hr)
  · unfold Safe at hsafe
    push Not at hsafe
    obtain ⟨a, ha, x, hx, hax⟩ := hsafe
    exact Or.inl (Or.inl ⟨a, ha, x, hx, hax⟩)

def Survives (w : List (Cell C A)) : Prop := ∀ v, Reach head w v → ¬ Zero v

lemma seek_missing (p : List (Cell C A)) (a : Cell C A) (s : List (Cell C A)) (x : C)
    (ha : a.color ≠ x) (hs : ∀ c ∈ s, c.check = .idle)
    (hn : ∀ c ∈ s, c.color ≠ x) :
    ∃ v, Reach head (p ++ setCheck a (.head x) :: s) v ∧ Zero v := by
  induction s generalizing p a with
  | nil =>
    refine ⟨_, .refl, Or.inr (Or.inr ⟨p, setCheck a (.head x), x, rfl, rfl, ha⟩)⟩
  | cons b s ih =>
    have hb : setCheck b .idle = b := by
      rw [← hs b (by simp)]; exact setCheck_self b
    have st : Step head (p ++ setCheck a (.head x) :: b :: s)
        ((p ++ [setCheck a (.passed x)]) ++ setCheck b (.head x) :: s) := by
      apply Or.inl
      simpa only [List.append_assoc, List.singleton_append, hb] using
        Edge.walk (head := head) p s a b x ha
    obtain ⟨v, hv, hz⟩ := ih (p ++ [setCheck a (.passed x)]) b
      (hn b (by simp)) (fun c hc => hs c (by simp [hc]))
      (fun c hc => hn c (by simp [hc]))
    exact ⟨v, .head st hv, hz⟩

theorem survives_all_colors {w : List (Cell C A)} (hne : w ≠ [])
    (hi : ∀ c ∈ w, c.check = .idle) (hv : Survives head w) :
    ∀ x, x ∈ w.map Cell.color := by
  classical
  intro x
  by_contra hn
  cases w with
  | nil => exact hne rfl
  | cons a s =>
    have hn' : ∀ c ∈ a :: s, c.color ≠ x := by
      simpa only [List.mem_map, not_exists, not_and] using hn
    have ha : setCheck a .idle = a := by
      rw [← hi a (by simp)]; exact setCheck_self a
    have st : Step head (a :: s) (setCheck a (.head x) :: s) := by
      apply Or.inl
      simpa only [ha] using Edge.create (head := head) a s x
    obtain ⟨v, hr, hz⟩ := seek_missing head [] a s x (hn' a (by simp))
      (fun c hc => hi c (by simp [hc])) (fun c hc => hn' c (by simp [hc]))
    exact hv v (.head st (by simpa using hr)) hz

lemma perm_reach (aux : A) (hn : ¬ head aux) {v w : List (Cell C A)} (h : v.Perm w)
    (hi : ∀ c ∈ v, c.check = .idle ∧ c.aux = aux) (p s : List (Cell C A)) :
    Reach head (p ++ v ++ s) (p ++ w ++ s) := by
  induction h generalizing p s with
  | nil => exact .refl
  | @cons a v w h ih =>
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      ih (fun c hc => hi c (by simp [hc])) (p ++ [a]) s
  | swap a b v =>
    have ha := hi a (by simp)
    have hb := hi b (by simp)
    have st : Step head (p ++ b :: a :: (v ++ s)) (p ++ a :: b :: (v ++ s)) :=
      Or.inl (Edge.swap p (v ++ s) b a (hb.1.trans ha.1.symm) (hb.2.trans ha.2.symm)
        (by simp [hb.1]) (by simpa [hb.2] using hn))
    simpa only [List.append_assoc, List.cons_append] using Relation.ReflTransGen.single st
  | @trans v w z h h' ih ih' =>
    exact (ih hi p s).trans (ih' (fun c hc => hi c (h.mem_iff.mpr hc)) p s)

theorem survives_distinct {w : List (Cell C A)} (aux : A) (hn : ¬ head aux)
    (hi : ∀ c ∈ w, c.check = .idle ∧ c.aux = aux) (hv : Survives head w) :
    (w.map Cell.color).Nodup := by
  classical
  by_contra hnd
  have hnd' : ¬ w.Nodup := by
    intro hd
    apply hnd
    apply hd.map_on
    intro a ha b hb heq
    have ha' := hi a ha
    have hb' := hi b hb
    cases a; cases b
    simp_all
  obtain ⟨a, ha⟩ := List.exists_duplicate_iff_not_nodup.mpr hnd'
  obtain ⟨s, hs⟩ := (List.duplicate_iff_sublist.mp ha).exists_perm_append
  have hr : Reach head w (a :: a :: s) := by
    simpa using perm_reach head aux hn hs hi [] []
  exact hv _ hr (Or.inr (Or.inl ⟨[], a, a, s, rfl, rfl⟩))

theorem survives_length [Fintype C] {w : List (Cell C A)} (hne : w ≠ [])
    (aux : A) (hn : ¬ head aux) (hi : ∀ c ∈ w, c.check = .idle ∧ c.aux = aux)
    (hv : Survives head w) : w.length = Fintype.card C := by
  classical
  have hd := survives_distinct head aux hn hi hv
  have hall := survives_all_colors head hne (fun c hc => (hi c hc).1) hv
  have heq : (w.map Cell.color).toFinset = Finset.univ := by
    ext x
    simp [hall x]
  have hc := List.toFinset_card_of_nodup hd
  simpa [heq] using hc.symm

theorem survives_enumeration {w : List (Cell C A)} (hne : w ≠ [])
    (aux : A) (hn : ¬ head aux) (hi : ∀ c ∈ w, c.check = .idle ∧ c.aux = aux)
    (hv : Survives head w) (enum : List C) (hd : enum.Nodup) (hall : ∀ x, x ∈ enum) :
    Reach head w (enum.map (fun x => Cell.mk x .idle aux)) := by
  classical
  have hnd := survives_distinct head aux hn hi hv
  have hw := survives_all_colors head hne (fun c hc => (hi c hc).1) hv
  have hperm : (w.map Cell.color).Perm enum :=
    List.perm_of_nodup_nodup_toFinset_eq hnd hd (by ext x; simp [hw x, hall x])
  have heq : (w.map Cell.color).map (fun x => Cell.mk x .idle aux) = w := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w]
    apply List.map_congr_left
    intro c hc
    obtain ⟨hc, ha⟩ := hi c hc
    cases c
    simp_all
  have hp := hperm.map (fun x => Cell.mk x .idle aux)
  rw [heq] at hp
  simpa using perm_reach head aux hn hp hi [] []

end SourceBurnside.Palette

end

end OAI

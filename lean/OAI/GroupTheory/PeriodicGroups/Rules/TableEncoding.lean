import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.HeadTour

namespace OAI

section
universe u v w
namespace SourceBurnside.LocalSyntax.Skeleton
variable {q k : ℕ}

lemma closed_idle_metadata (p s : List (Skeleton q k)) (c : Skeleton q k)
    (m : Metadata k) :
    Closed (p ++ ⟨c.pos,.idle,m⟩ :: s) ↔ Closed (p ++ c.mark .idle :: s) := by
  apply closed_replace_one
  · simp [Admissible]
  · intro a
    cases a with
    | none => simp [Link,leftExternal]
    | some a =>
      simp [Link,Pair,Structural,leftExternal,rightExternal,mark]
  · intro b
    cases b with
    | none => simp [Link,rightExternal]
    | some b =>
      simp [Link,Pair,Structural,leftExternal,rightExternal,mark]

lemma palette_link_left (c : Option (Skeleton q k)) (a : Skeleton q k) (x y : Fin q) :
    Link c (some {a with pos := .palette x}) ↔
      Link c (some {a with pos := .palette y}) := by
  cases c with
  | none => simp [Link,leftExternal,first]
  | some c =>
    cases h : c.pos <;>
      simp [Link,Pair,Structural,Internal,leftExternal,rightExternal,first,last,acceptsLeft,h]

lemma palette_link_right (a : Skeleton q k) (c : Option (Skeleton q k)) (x y : Fin q) :
    Link (some {a with pos := .palette x}) c ↔
      Link (some {a with pos := .palette y}) c := by
  cases c with
  | none => simp [Link,rightExternal,last]
  | some c =>
    cases h : c.pos <;>
      simp [Link,Pair,Structural,Internal,leftExternal,rightExternal,first,last,acceptsRight,h]

lemma closed_palette_color (p s : List (Skeleton q k)) (a : Skeleton q k) (x y : Fin q) :
    Closed (p ++ {a with pos := .palette x} :: s) ↔
      Closed (p ++ {a with pos := .palette y} :: s) := by
  apply closed_replace_one
  · simp [Admissible,first,last]
  · exact fun c => palette_link_left c a x y
  · exact fun c => palette_link_right a c x y

end SourceBurnside.LocalSyntax.Skeleton

namespace SourceBurnside.FiniteTable
open LocalSyntax
open LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q]

lemma unary_transaction_context {S : Schedule q} {a b : Cell q} (h : Unary S a b)
    (p s : List (Skeleton q 10)) :
    Closed (p ++ a.skeleton :: s) ↔ Closed (p ++ b.skeleton :: s) := by
  cases h with
  | create c side hc =>
    exact (closed_idle_metadata p s c.skeleton defaultMeta).trans
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
        (Skeleton.replacement_context (Skeleton.Replacement.create c.skeleton hc) p s))
  | finish_acquisition c side hc =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      (Skeleton.replacement_context (Skeleton.Replacement.finish c.skeleton hc) p s)
  | _ => exact Iff.rfl

lemma binary_transaction_context {S : Schedule q} {a b a' b' : Cell q}
    (h : Binary S a b a' b') (p s : List (Skeleton q 10)) :
    Closed (p ++ a.skeleton :: b.skeleton :: s) ↔
      Closed (p ++ a'.skeleton :: b'.skeleton :: s) := by
  cases h with
  | acquire a b side hp =>
    have hi := closed_idle_metadata (p ++ [a.skeleton.mark .boundary]) s b.skeleton defaultMeta
    have hh := (Skeleton.replacement_context (Skeleton.Replacement.acquire a.skeleton b.skeleton hp) p s)
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hi hh
    simpa only [Cell.boundary,Cell.wing,Cell.idle,Cell.pos] using hi.trans hh
  | read_left a b side j r hp =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      ((Skeleton.replacement_context (Skeleton.Replacement.sweep a.skeleton b.skeleton hp) p s)).symm
  | read_right a b side j r hp =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      (Skeleton.replacement_context (Skeleton.Replacement.sweep a.skeleton b.skeleton hp) p s)
  | undo_left a b side j r hp =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      ((Skeleton.replacement_context (Skeleton.Replacement.sweep a.skeleton b.skeleton hp) p s)).symm
  | undo_right a b side j r hp =>
    simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using
      (Skeleton.replacement_context (Skeleton.Replacement.sweep a.skeleton b.skeleton hp) p s)
  | checker_create => exact Iff.rfl
  | checker_advance => exact Iff.rfl
  | swap a b x y ha hb he hf hf' =>
    have hx : {a.skeleton with pos := .palette x} = a.skeleton := by
      cases a with | mk aa ac ad acf ah => cases aa; simp_all [Cell.pos]
    have hy : {a.skeleton with pos := .palette y} = b.skeleton := by
      exact congrArg Cell.skeleton he
    have h₁ := closed_palette_color p (b.skeleton :: s) a.skeleton x y
    have h₂ := closed_palette_color (p ++ [b.skeleton]) s a.skeleton y x
    rw [hx,hy] at h₁ h₂
    exact h₁.trans (by simpa only [List.append_assoc,List.cons_append,List.nil_append,Cell.boundary,Cell.full,Cell.wing,Cell.idle,Cell.pos] using h₂)

theorem replacement_transaction_context {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (h : Replacement S d v w) (p s : List (Cell q)) :
    Closed ((p ++ v ++ s).map Cell.skeleton) ↔
      Closed ((p ++ w ++ s).map Cell.skeleton) := by
  rcases h.2 with ⟨a,b,rfl,rfl,hh⟩ | ⟨a,b,a',b',rfl,rfl,hh⟩
  · simp only [List.map_append,List.map_cons,List.append_assoc,List.cons_append,List.nil_append]
    exact hh.elim (fun h => unary_transaction_context h _ _)
      (fun h => (unary_transaction_context h _ _).symm)
  · simp only [List.map_append,List.map_cons,List.append_assoc,List.cons_append,List.nil_append]
    exact hh.elim (fun h => binary_transaction_context h _ _)
      (fun h => (binary_transaction_context h _ _).symm)

end SourceBurnside.FiniteTable

namespace SourceBurnside.Palette
variable {C : Type*}
@[simp] lemma pair_from_idle (c : Check C) : Pair .idle c ↔ c=.idle := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .idle
@[simp] lemma pair_from_head (x : C) (c : Check C) : Pair (.head x) c ↔ c=.idle := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .rest x
@[simp] lemma pair_to_head (x : C) (c : Check C) : Pair c (.head x) ↔ c=.passed x := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .next x
@[simp] lemma pair_to_passed (x : C) (c : Check C) : Pair c (.passed x) ↔ c=.passed x := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .passed x
end SourceBurnside.Palette

namespace SourceBurnside.FiniteTable
open LocalSyntax
variable {q : ℕ} [NeZero q]

lemma unary_checker_context {S : Schedule q} {a b : Cell q} (h : Unary S a b)
    (p s : List (Cell q)) :
    List.IsChain CheckerPair (p ++ a :: s) ↔ List.IsChain CheckerPair (p ++ b :: s) := by
  apply chain_replace_one
  · intro c; cases h <;> exact Iff.rfl
  · intro c; cases h <;> exact Iff.rfl

omit [NeZero q] in
lemma checker_right_idle_head (b c : Cell q) (x : Fin q) :
    CheckerPair (b.setChecker .idle) c ↔ CheckerPair (b.setChecker (.head x)) c := by
  simp [CheckerPair,Cell.setChecker,Cell.isPalette,Cell.pos,Palette.LastOK]

omit [NeZero q] in
lemma checker_left_head_passed (a c : Cell q) (x : Fin q) :
    CheckerPair c (a.setChecker (.head x)) ↔ CheckerPair c (a.setChecker (.passed x)) := by
  simp [CheckerPair,Cell.setChecker,Cell.isPalette,Cell.pos]

omit [NeZero q] in
lemma checker_color_left (a c : Cell q) (x y : Fin q) :
    CheckerPair c (a.setColor x) ↔ CheckerPair c (a.setColor y) := by
  simp [CheckerPair,Cell.setColor,Cell.isPalette,Cell.pos]

omit [NeZero q] in
lemma checker_color_right (a c : Cell q) (x y : Fin q) :
    CheckerPair (a.setColor x) c ↔ CheckerPair (a.setColor y) c := by
  simp [CheckerPair,Cell.setColor,Cell.isPalette,Cell.pos]

lemma binary_checker_context {S : Schedule q} {a b a' b' : Cell q}
    (h : Binary S a b a' b') (p s : List (Cell q)) :
    List.IsChain CheckerPair (p ++ a :: b :: s) ↔
      List.IsChain CheckerPair (p ++ a' :: b' :: s) := by
  cases h with
  | acquire | read_left | read_right | undo_left | undo_right =>
    apply chain_replace_two <;> intros <;> exact Iff.rfl
  | checker_create a b r x ha hr hb =>
    apply chain_replace_two
    · intro c; exact Iff.rfl
    · exact fun c => checker_right_idle_head b c x
    · have hap : ¬ a.isPalette := by simp [Cell.isPalette,ha]
      rcases hb with ⟨v,hv⟩
      simp [CheckerPair,Cell.setChecker,Cell.isPalette,Cell.pos,
        show a.skeleton.pos = .core r from ha]
  | checker_advance a b v x ha hb hv =>
    apply chain_replace_two
    · exact fun c => checker_left_head_passed a c x
    · exact fun c => checker_right_idle_head b c x
    · rcases hb with ⟨y,hy⟩
      simp [CheckerPair,Cell.setChecker,Cell.isPalette,Cell.pos,
        Palette.LastOK,show b.skeleton.pos = .palette y from hy]
  | swap a b x y ha hb he hf hf' =>
    have hx : a.setColor x = a := by
      cases a with
      | mk aa ac ad ace ah => cases aa; simp_all [Cell.pos,Cell.setColor]
    apply chain_replace_two
    · intro c
      have hh := checker_color_left a c x y
      simpa only [hx,he] using hh
    · intro c
      have hh := checker_color_right a c y x
      simpa only [hx,he] using hh
    · have h₁ := checker_color_right a b x y
      have h₂ := checker_color_left a b y x
      rw [hx,he] at h₁ h₂
      exact h₁.trans h₂

theorem replacement_checker_context {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (h : Replacement S d v w) (p s : List (Cell q)) :
    List.IsChain CheckerPair (p ++ v ++ s) ↔ List.IsChain CheckerPair (p ++ w ++ s) := by
  rcases h.2 with ⟨a,b,rfl,rfl,hh⟩ | ⟨a,b,a',b',rfl,rfl,hh⟩
  · simp only [List.append_assoc,List.cons_append,List.nil_append]
    exact hh.elim (fun h => unary_checker_context h _ _)
      (fun h => (unary_checker_context h _ _).symm)
  · simp only [List.append_assoc,List.cons_append,List.nil_append]
    exact hh.elim (fun h => binary_checker_context h _ _)
      (fun h => (binary_checker_context h _ _).symm)

def Syntax (S : Schedule q) (d : ℕ) (w : List (Cell q)) : Prop :=
  LocalSyntax.Skeleton.Closed (w.map Cell.skeleton) ∧
    List.IsChain CheckerPair w ∧ ∀ c ∈ w, c.Format S d

theorem replacement_syntax_context {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (h : Replacement S d v w) (p s : List (Cell q)) :
    Syntax S d (p ++ v ++ s) ↔ Syntax S d (p ++ w ++ s) := by
  have hv : ∀ c ∈ v, c.Format S d := fun c hc => h.1 c (List.mem_append_left _ hc)
  have hw : ∀ c ∈ w, c.Format S d := fun c hc => h.1 c (List.mem_append_right _ hc)
  unfold Syntax
  rw [replacement_transaction_context h, replacement_checker_context h]
  simp only [List.forall_mem_append]
  tauto

def Step (S : Schedule q) (d : ℕ) (v w : List (Cell q)) : Prop :=
  ∃ p s a b, v=p++a++s ∧ w=p++b++s ∧ Replacement S d a b

abbrev Reach (S : Schedule q) (d : ℕ) := Relation.ReflTransGen (Step S d)

theorem reach_syntax {S : Schedule q} {d : ℕ} {v w : List (Cell q)}
    (h : Reach S d v w) (hv : Syntax S d v) : Syntax S d w := by
  induction h with
  | refl => exact hv
  | tail h e ih =>
    rcases e with ⟨p,s,a,b,rfl,rfl,he⟩
    exact (replacement_syntax_context he p s).mp ih

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

lemma step_symm {v w : List (Cell q)} (h : Step S d v w) : Step S d w v := by
  rcases h with ⟨p,s,a,b,hv,hw,hh⟩
  exact ⟨p,s,b,a,hw,hv,(replacement_symm S d a b).mp hh⟩

lemma step_context {v w : List (Cell q)} (h : Step S d v w) (p s : List (Cell q)) :
    Step S d (p++v++s) (p++w++s) := by
  rcases h with ⟨l,r,a,b,rfl,rfl,hh⟩
  exact ⟨p++l,r++s,a,b,by simp only [List.append_assoc],
    by simp only [List.append_assoc],hh⟩

lemma reach_symm {v w : List (Cell q)} (h : Reach S d v w) : Reach S d w v := by
  induction h with
  | refl => exact .refl
  | tail h e ih => exact (Relation.ReflTransGen.single (step_symm e)).trans ih

lemma reach_context {v w : List (Cell q)} (h : Reach S d v w) (p s : List (Cell q)) :
    Reach S d (p++v++s) (p++w++s) := by
  induction h with
  | refl => exact .refl
  | tail h e ih => exact ih.tail (step_context e p s)

lemma step_length {v w : List (Cell q)} (h : Step S d v w) : v.length=w.length := by
  rcases h with ⟨p,s,a,b,rfl,rfl,hh⟩
  simp only [List.length_append,(replacement_lengths S d a b hh).1]

lemma reach_length {v w : List (Cell q)} (h : Reach S d v w) : v.length=w.length := by
  induction h with
  | refl => rfl
  | tail h e ih => exact ih.trans (step_length e)

def repRel (S : Schedule q) (d : ℕ) (v w : FreeMonoid (Cell q)) : Prop :=
  Replacement S d v.toList w.toList

def reachCon (S : Schedule q) (d : ℕ) : Con (FreeMonoid (Cell q)) where
  r v w := Reach S d v.toList w.toList
  iseqv := ⟨fun _ => .refl,fun h => reach_symm h,fun h k => h.trans k⟩
  mul' := by
    intro a b c e hab hce
    change Reach S d (a.toList++c.toList) (b.toList++e.toList)
    have h₁ : Reach S d (a.toList++c.toList) (b.toList++c.toList) := by
      simpa using reach_context hab [] c.toList
    have h₂ : Reach S d (b.toList++c.toList) (b.toList++e.toList) := by
      simpa using reach_context hce b.toList []
    exact h₁.trans h₂

theorem reach_iff_conGen {v w : List (Cell q)} :
    Reach S d v w ↔ conGen (repRel S d) (FreeMonoid.ofList v) (FreeMonoid.ofList w) := by
  constructor
  · intro h
    induction h with
    | refl => exact (conGen (repRel S d)).refl _
    | tail h e ih =>
      rcases e with ⟨p,s,a,b,rfl,rfl,hh⟩
      apply (conGen (repRel S d)).trans ih
      exact (conGen (repRel S d)).mul
        ((conGen (repRel S d)).mul ((conGen (repRel S d)).refl (FreeMonoid.ofList p))
          (ConGen.Rel.of (FreeMonoid.ofList a) (FreeMonoid.ofList b) hh))
        ((conGen (repRel S d)).refl (FreeMonoid.ofList s))
  · intro h
    have he : conGen (repRel S d) ≤ reachCon S d := by
      apply Con.conGen_le.mpr
      intro a b hh
      exact Relation.ReflTransGen.single ⟨[],[],a.toList,b.toList,by simp,by simp,hh⟩
    exact he h

lemma unary_idle_first {a b : Cell q} (h : Unary S a b) (ha : a.marker=.idle) :
    ∃ p, a.pos=.core p ∧ p.val=0 := by
  cases h <;> simp [Cell.idle,Cell.boundary,Cell.full,Cell.marker,
    Skeleton.mark] at ha
  case create c s hf => exact hf.2

lemma unary_ne_idle_right {a b : Cell q} (h : Unary S a b) : b.marker ≠ .idle := by
  cases h <;> simp [Cell.boundary,Cell.full,Cell.marker,Skeleton.mark]

lemma no_step_interior_idle {c : Cell q} (hm : c.marker=.idle)
    (hp : ∃ p, c.pos=.core p ∧ p.val ≠ 0) (w : List (Cell q)) : ¬Step S d [c] w := by
  rintro ⟨l,r,a,b,he,hw,hh⟩
  have hl := congrArg List.length he
  have hn := (replacement_lengths S d a b hh).2.1
  simp only [List.length_singleton,List.length_append] at hl
  have hll : l=[] := List.length_eq_zero_iff.mp (by omega)
  have hrr : r=[] := List.length_eq_zero_iff.mp (by omega)
  subst l; subst r
  simp only [List.nil_append,List.append_nil] at he hw
  subst a; subst w
  rcases hh.2 with ⟨a,b,he,rfl,hh⟩ | ⟨a,b,a',b',he,hw,hh⟩
  · have hca : c=a := by simpa using he
    subst a
    rcases hh with hh | hh
    · rcases unary_idle_first hh hm with ⟨p,hp',hv⟩
      rcases hp with ⟨r,hr,hn⟩
      have he : r=p := by simpa [hr] using hp'
      exact hn (he.symm ▸ hv)
    · exact unary_ne_idle_right hh hm
  · simp at he

theorem reach_interior_idle_iff {c : Cell q} (hm : c.marker=.idle)
    (hp : ∃ p, c.pos=.core p ∧ p.val ≠ 0) (w : List (Cell q)) :
    Reach S d [c] w ↔ w=[c] := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail h e ih => exact (no_step_interior_idle hm hp _ (ih ▸ e)).elim
  · rintro rfl; exact .refl

def idleCore (p : Fin q) : Cell q :=
  ⟨⟨.core p,.idle,defaultMeta⟩,.idle,0,0,defaultHead⟩

lemma idleCore_format (p : Fin q) : (idleCore p).Format S d := by
  simp [Cell.Format,idleCore,Skeleton.Admissible,Cell.isPalette,Cell.isCore,
    Cell.pos,Cell.marker,Cell.metadata,IsHead]

lemma idleCore_not_zero (p : Fin q) : ¬ UnaryZero S d (idleCore p) := by
  rintro (h | h | ⟨x,h,_⟩)
  · exact h (idleCore_format p)
  · simp [SemanticZero,idleCore,Cell.marker] at h
  · simp [idleCore,Cell.pos] at h

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q]

def shortWords (q : ℕ) : Set (FreeMonoid (Cell q)) :=
  Set.range (fun c : Cell q => FreeMonoid.ofList [c]) ∪
    Set.range (fun c : Cell q × Cell q => FreeMonoid.ofList [c.1,c.2])

omit [NeZero q] in
lemma shortWords_finite : (shortWords q).Finite :=
  (Set.finite_range _).union (Set.finite_range _)

lemma replacement_mem_short {S : Schedule q} {d : ℕ}
    {v w : FreeMonoid (Cell q)} (h : repRel S d v w) :
    v ∈ shortWords q ∧ w ∈ shortWords q := by
  rcases h.2 with ⟨a,b,hv,hw,_⟩ | ⟨a,b,a',b',hv,hw,_⟩
  · exact ⟨Or.inl ⟨a,(congrArg FreeMonoid.ofList hv).symm⟩,
      Or.inl ⟨b,(congrArg FreeMonoid.ofList hw).symm⟩⟩
  · exact ⟨Or.inr ⟨(a,b),(congrArg FreeMonoid.ofList hv).symm⟩,
      Or.inr ⟨(a',b'),(congrArg FreeMonoid.ofList hw).symm⟩⟩

lemma replacement_finite (S : Schedule q) (d : ℕ) :
    {vw : FreeMonoid (Cell q) × FreeMonoid (Cell q) | repRel S d vw.1 vw.2}.Finite :=
  (shortWords_finite.prod shortWords_finite).subset (fun _ h => replacement_mem_short h)

lemma zero_mem_short {S : Schedule q} {d : ℕ}
    {v : FreeMonoid (Cell q)} (h : Zero S d v.toList) : v ∈ shortWords q := by
  rcases h with ⟨c,hc,_⟩ | ⟨a,b,hc,_⟩
  · exact Or.inl ⟨c,(congrArg FreeMonoid.ofList hc).symm⟩
  · exact Or.inr ⟨(a,b),(congrArg FreeMonoid.ofList hc).symm⟩

lemma zero_finite (S : Schedule q) (d : ℕ) :
    {v : FreeMonoid (Cell q) | Zero S d v.toList}.Finite :=
  shortWords_finite.subset (fun _ h => zero_mem_short h)

theorem idleCore_not_contextual_zero (S : Schedule q) (d : ℕ) (p : Fin q)
    (l z r : List (Cell q)) (hz : Zero S d z) :
    [idleCore p] ≠ l++z++r := by
  intro he
  have hl := congrArg List.length he
  have hn := (zero_lengths S d z hz).1
  simp only [List.length_singleton,List.length_append] at hl
  have hll : l=[] := List.length_eq_zero_iff.mp (by omega)
  have hrr : r=[] := List.length_eq_zero_iff.mp (by omega)
  subst l; subst r
  simp only [List.nil_append,List.append_nil] at he
  subst z
  rcases hz with ⟨c,he,hc⟩ | ⟨a,b,he,_⟩
  · have hc' : idleCore p=c := by simpa using he
    exact idleCore_not_zero p (hc'.symm ▸ hc)
  · simp at he

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax

abbrev Raw (h : ℕ) := Fin (10000*h) → Bool

lemma reserve_lt {h : ℕ} (hh : 0 < h) : 64*h+512 ≤ 10000*h := by omega

def intPosition {h : ℕ} (_hh : 0 < h) (s : Fin 32) (i : Fin (2*h)) : Fin (10000*h) :=
  ⟨s.val*(2*h)+i.val,by
    have hs : s.val≤31 := by omega
    have hm := Nat.mul_le_mul_right (2*h) hs
    have := i.isLt
    omega⟩
def flagPosition {h : ℕ} (hh : 0 < h) (i : Fin 512) : Fin (10000*h) :=
  ⟨64*h+i.val,by have := reserve_lt hh; have := i.isLt; omega⟩

def write {h : ℕ} (ints : Fin 32 → ℕ) (flags : Fin 512 → Bool) : Raw h := fun i =>
  if hi : i.val < 64*h then
    (ints ⟨i.val/(2*h),by
      have hi' : i.val < 32*(2*h) := by omega
      exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hi'⟩).testBit (i.val%(2*h))
  else if hf : i.val < 64*h+512 then flags ⟨i.val-64*h,by omega⟩ else false

def readInt {h : ℕ} (hh : 0 < h) (w : Raw h) (s : Fin 32) : ℕ :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => w (intPosition hh s i)))).toNat

def readFlag {h : ℕ} (hh : 0 < h) (w : Raw h) (i : Fin 512) : Bool := w (flagPosition hh i)

lemma write_int {h : ℕ} (hh : 0 < h) (ints : Fin 32 → ℕ) (flags : Fin 512 → Bool)
    (s : Fin 32) (i : Fin (2*h)) :
    write (h:=h) ints flags (intPosition hh s i) = (ints s).testBit i.val := by
  have hi : s.val*(2*h)+i.val < 64*h := by
    have hs : s.val≤31 := by omega
    have hm := Nat.mul_le_mul_right (2*h) hs
    have := i.isLt
    omega
  have hd : (s.val*(2*h)+i.val)/(2*h)=s.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega)]
    simp [Nat.div_eq_of_lt i.isLt]
  have hm : (s.val*(2*h)+i.val)%(2*h)=i.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
  simp [write,intPosition,hi,hd,hm]

lemma readFlag_write {h : ℕ} (hh : 0 < h) (ints : Fin 32 → ℕ) (flags : Fin 512 → Bool)
    (i : Fin 512) : readFlag hh (write ints flags) i=flags i := by
  have hi := i.isLt
  simp [readFlag,write,flagPosition,show ¬64*h+i.val < 64*h by omega,
    show 64*h+i.val < 64*h+512 by omega]

lemma readInt_write {h : ℕ} (hh : 0 < h) (ints : Fin 32 → ℕ) (flags : Fin 512 → Bool)
    (s : Fin 32) (hs : ints s < 2^(2*h)) : readInt hh (write ints flags) s=ints s := by
  let bs := List.ofFn (fun i : Fin (2*h) => (ints s).testBit i.val)
  have he : (List.ofFn fun i => write ints flags (intPosition hh s i))=bs := by
    apply congrArg List.ofFn
    funext i
    exact write_int hh ints flags s i
  have hv : BitVec.ofBoolListLE bs = BitVec.ofNat bs.length (ints s) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi' : i < 2*h := by simpa [bs] using hi
    rw [BitVec.getLsbD_ofBoolListLE,BitVec.getLsbD_ofNat]
    simp [bs,hi']
  unfold readInt
  rw [he,hv]
  simp [bs,Nat.mod_eq_of_lt hs]

def positionTag {q : ℕ} : Position q → ℕ
  | .core _ => 0 | .palette _ => 1 | .stop => 2
def positionIndex {q : ℕ} : Position q → ℕ
  | .core p => p.val | .palette a => a.val | .stop => 0
def markerTag : Marker → ℕ
  | .idle => 0 | .left => 1 | .boundary => 2 | .full => 3 | .right => 4
def checkerTag {q : ℕ} : Palette.Check (Fin q) → ℕ
  | .idle => 0 | .passed _ => 1 | .head _ => 2
def checkerIndex {q : ℕ} : Palette.Check (Fin q) → ℕ
  | .idle => 0 | .passed x => x.val | .head x => x.val
def phaseTag : Phase → ℕ
  | .acquisition => 0 | .readLeft => 1 | .readRight => 2 | .beforeGate => 3
  | .afterGate => 4 | .undoLeft => 5 | .undoRight => 6 | .finish => 7 | .success => 8

def bit (x : ZMod 2) : Bool := decide (x=1)
def unbit (b : Bool) : ZMod 2 := if b then 1 else 0
@[simp] lemma unbit_bit (x : ZMod 2) : unbit (bit x)=x := by
  have hx : x=0 ∨ x=1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with rfl | rfl <;> norm_num [unbit,SourceBurnside.FiniteTable.Codec.bit]
@[simp] lemma bit_unbit (b : Bool) : bit (unbit b)=b := by cases b <;> decide

def integers {q : ℕ} (c : Cell q) (s : Fin 32) : ℕ := match s.val with
  | 0 => positionTag c.pos
  | 1 => positionIndex c.pos
  | 2 => markerTag c.marker
  | 3 => c.metadata.arity.val
  | 4 => c.metadata.block.val
  | 5 => checkerTag c.checker
  | 6 => checkerIndex c.checker
  | 7 => c.head.clause.val
  | 8 => phaseTag c.head.phase
  | _ => 0

def flags {q : ℕ} (c : Cell q) (i : Fin 512) : Bool := match i.val with
  | 0 => c.metadata.zeroTask
  | 1 => c.head.side
  | 2 => bit (c.data false)
  | 3 => bit (c.data true)
  | 4 => bit c.certificate
  | 5 => bit (c.head.reg 0)
  | 6 => bit (c.head.reg 1)
  | 7 => bit (c.head.reg 2)
  | _ => false

def encode {h : ℕ} (c : Cell (2^h)) : Raw h := write (integers c) (flags c)

def getFin (n i : ℕ) : Option (Fin n) := if hi : i < n then some ⟨i,hi⟩ else none
@[simp] lemma getFin_val {n : ℕ} (i : Fin n) : getFin n i.val=some i := by simp [getFin,i.isLt]

def getPosition (q t i : ℕ) : Option (Position q) := match t with
  | 0 => .map Position.core (getFin q i)
  | 1 => .map Position.palette (getFin q i)
  | 2 => if i=0 then some .stop else none
  | _ => none

def getMarker : ℕ → Option Marker
  | 0 => some .idle | 1 => some .left | 2 => some .boundary
  | 3 => some .full | 4 => some .right | _ => none

def getChecker (q t i : ℕ) : Option (Palette.Check (Fin q)) := match t with
  | 0 => if i=0 then some .idle else none
  | 1 => .map Palette.Check.passed (getFin q i)
  | 2 => .map Palette.Check.head (getFin q i)
  | _ => none

def getPhase : ℕ → Option Phase
  | 0 => some .acquisition | 1 => some .readLeft | 2 => some .readRight
  | 3 => some .beforeGate | 4 => some .afterGate | 5 => some .undoLeft
  | 6 => some .undoRight | 7 => some .finish | 8 => some .success | _ => none

@[simp] lemma getPosition_encode {q : ℕ} (p : Position q) :
    getPosition q (positionTag p) (positionIndex p)=some p := by
  cases p <;> simp [getPosition,positionTag,positionIndex]
@[simp] lemma getMarker_encode (m : Marker) : getMarker (markerTag m)=some m := by cases m <;> rfl
@[simp] lemma getChecker_encode {q : ℕ} (c : Palette.Check (Fin q)) :
    getChecker q (checkerTag c) (checkerIndex c)=some c := by
  cases c <;> simp [getChecker,checkerTag,checkerIndex]
@[simp] lemma getPhase_encode (p : Phase) : getPhase (phaseTag p)=some p := by cases p <;> rfl

def parse {h : ℕ} (hh : 0 < h) (w : Raw h) : Option (Cell (2^h)) := do
  let ints := readInt hh w
  let fl := readFlag hh w
  let pos ← getPosition (2^h) (ints 0) (ints 1)
  let marker ← getMarker (ints 2)
  let arity ← getFin 10 (ints 3)
  let block ← getFin (arity.val+1) (ints 4)
  let checker ← getChecker (2^h) (ints 5) (ints 6)
  let clause ← getFin (2^h) (ints 7)
  let phase ← getPhase (ints 8)
  return ⟨⟨pos,marker,⟨arity,fl 0,block⟩⟩,checker,
    (fun s => unbit (if s then fl 3 else fl 2)),unbit (fl 4),
    ⟨fl 1,clause,phase,![unbit (fl 5),unbit (fl 6),unbit (fl 7)]⟩⟩

def decode {h : ℕ} (hh : 0 < h) (w : Raw h) : Option (Cell (2^h)) := do
  let c ← parse hh w
  if w=encode c then some c else none

lemma positionTag_lt {q : ℕ} (p : Position q) : positionTag p < 3 := by cases p <;> simp [positionTag]
lemma positionIndex_lt {q : ℕ} (hq : 0 < q) (p : Position q) : positionIndex p < q := by
  cases p with
  | core p => exact p.isLt
  | palette a => exact a.isLt
  | stop => exact hq
lemma markerTag_lt (m : Marker) : markerTag m < 5 := by cases m <;> decide
lemma checkerTag_lt {q : ℕ} (c : Palette.Check (Fin q)) : checkerTag c < 3 := by cases c <;> simp [checkerTag]
lemma checkerIndex_lt {q : ℕ} (hq : 0 < q) (c : Palette.Check (Fin q)) : checkerIndex c < q := by
  cases c with
  | idle => exact hq
  | passed x => exact x.isLt
  | head x => exact x.isLt
lemma phaseTag_lt (p : Phase) : phaseTag p < 9 := by cases p <;> decide

lemma integers_lt {q : ℕ} (hq : 10≤q) (c : Cell q) (s : Fin 32) : integers c s < q := by
  unfold integers
  split
  · exact (positionTag_lt _).trans_le (by omega)
  · exact positionIndex_lt (by omega) _
  · exact (markerTag_lt _).trans_le (by omega)
  · exact c.metadata.arity.isLt.trans_le hq
  · have ha := c.metadata.arity.isLt
    have hb := c.metadata.block.isLt
    omega
  · exact (checkerTag_lt _).trans_le (by omega)
  · exact checkerIndex_lt (by omega) _
  · exact c.head.clause.isLt
  · exact (phaseTag_lt _).trans_le (by omega)
  · omega

lemma readInt_encode {h : ℕ} (hh : 4≤h) (c : Cell (2^h)) (s : Fin 32) :
    readInt (by omega) (encode c) s=integers c s := by
  apply readInt_write
  have hq : 10≤2^h := by
    have ht := Nat.pow_le_pow_right (show 0 < 2 by omega) hh
    norm_num at ht
    omega
  have hm := Nat.pow_le_pow_right (show 0 < 2 by omega) (show h≤2*h by omega)
  exact (integers_lt hq c s).trans_le hm

lemma readFlag_encode {h : ℕ} (hh : 0 < h) (c : Cell (2^h)) (s : Fin 512) :
    readFlag hh (encode c) s=flags c s := readFlag_write hh _ _ _

lemma parse_encode {h : ℕ} (hh : 4≤h) (c : Cell (2^h)) : parse (by omega) (encode c)=some c := by
  have hi : readInt (by omega) (encode c)=integers c := funext (readInt_encode hh c)
  have hf : readFlag (by omega) (encode c)=flags c := funext (readFlag_encode (by omega) c)
  have hd : (fun s => unbit (if s then bit (c.data true) else bit (c.data false)))=c.data := by
    funext s; cases s <;> simp
  have hr : ![c.head.reg 0,c.head.reg 1,c.head.reg 2]=c.head.reg := by
    funext i; fin_cases i <;> simp
  simp [parse,hi,hf,integers,flags,hd,hr,Cell.pos,Cell.marker,Cell.metadata]

lemma decode_encode {h : ℕ} (hh : 4≤h) (c : Cell (2^h)) : decode (by omega) (encode c)=some c := by
  simp [decode,parse_encode hh]

lemma encode_injective {h : ℕ} (hh : 4≤h) : Function.Injective (encode (h:=h)) := by
  intro c d he
  have hc := decode_encode hh c
  have hd := decode_encode hh d
  rw [he,hd] at hc
  exact Option.some.inj hc.symm

lemma decode_eq_some_iff {h : ℕ} (hh : 4≤h) (w : Raw h) (c : Cell (2^h)) :
    decode (by omega) w=some c ↔ w=encode c := by
  constructor
  · unfold decode
    cases hp : parse (by omega) w with
    | none => simp
    | some d =>
      change (if w=encode d then some d else none)=some c → _
      split
      · intro he
        cases Option.some.inj he
        assumption
      · simp
  · rintro rfl
    exact decode_encode hh c

lemma raw_card (h : ℕ) : Fintype.card (Raw h)=2^(10000*h) := by simp [Raw]

def decodeWord {h : ℕ} (hh : 0 < h) : List (Raw h) → Option (List (Cell (2^h)))
  | [] => some []
  | a::w => do
    let c ← decode hh a
    let cs ← decodeWord hh w
    return c::cs

lemma decodeWord_encode {h : ℕ} (hh : 4≤h) (w : List (Cell (2^h))) :
    decodeWord (by omega) (w.map encode)=some w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [decodeWord,decode_encode hh,ih]

lemma decodeWord_eq_some_iff {h : ℕ} (hh : 4≤h) (v : List (Raw h)) (w : List (Cell (2^h))) :
    decodeWord (by omega) v=some w ↔ v=w.map encode := by
  induction v generalizing w with
  | nil => cases w <;> simp [decodeWord]
  | cons a v ih =>
    cases ha : decode (by omega) a with
    | none =>
      have hne : ∀ b : Cell (2^h), a≠encode b := by
        intro b he
        have hx := decode_encode hh b
        rw [he] at ha
        rw [ha] at hx
        contradiction
      cases w <;> simp [decodeWord,ha,hne]
    | some b =>
      have hab : a=encode b := (decode_eq_some_iff hh a b).mp ha
      cases hv : decodeWord (by omega) v with
      | none =>
        have hne : ∀ z : List (Cell (2^h)), v≠z.map encode := by
          intro z hz
          have hz' := (ih z).mpr hz
          rw [hv] at hz'
          contradiction
        cases w <;> simp [decodeWord,ha,hv,hne]
      | some z =>
        have hvz : v=z.map encode := (ih z).mp hv
        simp only [decodeWord,ha,hv]
        rw [hab,hvz,← List.map_cons]
        change some (b::z)=some w ↔ (b::z).map encode=w.map encode
        rw [Option.some.injEq]
        exact (encode_injective hh).list_map.eq_iff.symm

def unaryZero {h : ℕ} (hh : 0 < h) (S : Schedule (2^h)) (d : ℕ) (a : Raw h) : Prop :=
  match decode hh a with
  | none => True
  | some c => UnaryZero S d c

def binaryZero {h : ℕ} (hh : 0 < h) (a b : Raw h) : Prop :=
  match decode hh a, decode hh b with
  | some c,some d => BinaryZero c d
  | _,_ => False

def replacement {h : ℕ} (hh : 0 < h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Raw h)) : Prop :=
  match decodeWord hh v,decodeWord hh w with
  | some a,some b => Replacement S d a b
  | _,_ => False

def zero {h : ℕ} (hh : 0 < h) (S : Schedule (2^h)) (d : ℕ) (v : List (Raw h)) : Prop :=
  match v with
  | [a] => unaryZero hh S d a
  | [a,b] => binaryZero hh a b
  | _ => False

lemma unaryZero_encode {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ) (a : Cell (2^h)) :
    unaryZero (by omega) S d (encode a) ↔ UnaryZero S d a := by
  simp [unaryZero,decode_encode hh]
lemma binaryZero_encode {h : ℕ} (hh : 4≤h) (a b : Cell (2^h)) :
    binaryZero (by omega) (encode a) (encode b) ↔ BinaryZero a b := by
  simp [binaryZero,decode_encode hh]
lemma replacement_encode {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Cell (2^h))) :
    replacement (by omega) S d (v.map encode) (w.map encode) ↔ Replacement S d v w := by
  simp [replacement,decodeWord_encode hh]
lemma zero_encode {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ) (v : List (Cell (2^h))) :
    zero (by omega) S d (v.map encode) ↔ Zero S d v := by
  cases v with
  | nil => simp [zero,Zero]
  | cons a v =>
    cases v with
    | nil => simp [zero,Zero,unaryZero_encode hh]
    | cons b v =>
      cases v <;> simp [zero,Zero,binaryZero_encode hh]

lemma replacement_has_encodings {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Raw h)) (hv : replacement (by omega) S d v w) :
    ∃ a b, v=a.map encode ∧ w=b.map encode ∧ Replacement S d a b := by
  unfold replacement at hv
  cases ha : decodeWord (by omega) v with
  | none => simp [ha] at hv
  | some a =>
    cases hb : decodeWord (by omega) w with
    | none => simp [ha,hb] at hv
    | some b =>
      exact ⟨a,b,(decodeWord_eq_some_iff hh v a).mp ha,
        (decodeWord_eq_some_iff hh w b).mp hb,by simpa [ha,hb] using hv⟩

lemma replacement_lengths {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Raw h)) (hv : replacement (by omega) S d v w) :
    v.length=w.length ∧ 1≤v.length ∧ v.length≤2 := by
  obtain ⟨a,b,rfl,rfl,hab⟩ := replacement_has_encodings hh S d v w hv
  simpa using FiniteTable.replacement_lengths S d a b hab

lemma zero_lengths {h : ℕ} (hh : 0 < h) (S : Schedule (2^h)) (d : ℕ)
    (v : List (Raw h)) (hv : zero hh S d v) : 1≤v.length ∧ v.length≤2 := by
  cases v with
  | nil => simp [zero] at hv
  | cons a v =>
    cases v with
    | nil => simp
    | cons b v =>
      cases v with
      | nil => simp
      | cons c v => simp [zero] at hv

end SourceBurnside.FiniteTable.Codec

end

end OAI

import Mathlib

namespace OAI

/-!
Newman normalization, block coding, canonical representatives, and static tests.
-/

/- Rewriting layer for the self-reference construction.  No assumptions on
   either main theorem are introduced here. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation

section Newman
variable {α : Type*} (R : α → α → Prop)

def Irreducible (a : α) : Prop := ∀ b, ¬ R a b

theorem exists_irreducible (wf : WellFounded (flip R)) (a : α) :
    ∃ b, ReflTransGen R a b ∧ Irreducible R b := by
  classical
  induction a using wf.induction with
  | h a ih =>
    by_cases ha : Irreducible R a
    · exact ⟨a, .refl, ha⟩
    · obtain ⟨b, hab⟩ := not_forall.mp ha
      have hab : R a b := Classical.not_not.mp hab
      obtain ⟨c, hbc, hc⟩ := ih b hab
      exact ⟨c, (ReflTransGen.single hab).trans hbc, hc⟩

theorem irreducible_reaches {a b : α} (ha : Irreducible R a)
    (hab : ReflTransGen R a b) : a = b := by
  rcases hab.cases_head with hab | ⟨c,hac,_⟩
  · exact hab
  · exact False.elim (ha c hac)

/-- Newman's induction, with the terminal-descendant existence made explicit. -/
theorem normal_unique (wf : WellFounded (flip R))
    (localJoin : ∀ a b c, R a b → R a c → Join (ReflTransGen R) b c)
    (a : α) : ∀ b c, ReflTransGen R a b → ReflTransGen R a c →
      Irreducible R b → Irreducible R c → b = c := by
  induction a using wf.induction with
  | h a ih =>
    intro b c hab hac hb hc
    rcases hab.cases_head with rfl | ⟨b₁,hab₁,hb₁b⟩
    · exact irreducible_reaches R hb hac
    rcases hac.cases_head with rfl | ⟨c₁,hac₁,hc₁c⟩
    · exact (irreducible_reaches R hc (.head hab₁ hb₁b)).symm
    obtain ⟨d,hb₁d,hc₁d⟩ := localJoin a b₁ c₁ hab₁ hac₁
    obtain ⟨e,hde,he⟩ := exists_irreducible R wf d
    exact (ih b₁ hab₁ b e hb₁b (hb₁d.trans hde) hb he).trans
      (ih c₁ hac₁ c e hc₁c (hc₁d.trans hde) hc he).symm

theorem newman (wf : WellFounded (flip R))
    (localJoin : ∀ a b c, R a b → R a c → Join (ReflTransGen R) b c)
    {a b c : α} (hab : ReflTransGen R a b) (hac : ReflTransGen R a c) :
    Join (ReflTransGen R) b c := by
  obtain ⟨u,hbu,hu⟩ := exists_irreducible R wf b
  obtain ⟨v,hcv,hv⟩ := exists_irreducible R wf c
  have h := normal_unique R wf localJoin a u v (hab.trans hbu) (hac.trans hcv) hu hv
  exact ⟨u,hbu,h ▸ hcv⟩
end Newman

variable {S : Type*}

/-- One directed rule in an arbitrary two-sided context. -/
inductive Step (rules : List (List S × List S)) : List S → List S → Prop
  | apply {u v} (h : (u,v) ∈ rules) (x y) : Step rules (x++u++y) (x++v++y)

abbrev Steps (rules : List (List S × List S)) := ReflTransGen (Step rules)

theorem step_context {rules : List (List S × List S)} {u v : List S}
    (h : Step rules u v) (x y : List S) : Step rules (x++u++y) (x++v++y) := by
  cases h with
  | apply h a b => simpa only [List.append_assoc] using Step.apply h (x++a) (b++y)

theorem steps_context {rules : List (List S × List S)} {u v : List S}
    (h : Steps rules u v) (x y : List S) : Steps rules (x++u++y) (x++v++y) :=
  h.lift (fun w => x++w++y) (fun _ _ h => step_context h x y)

theorem lex_append_suffix {r : S → S → Prop} {u v : List S}
    (h : List.Lex r u v) (hlen : u.length = v.length) (y : List S) :
    List.Lex r (u++y) (v++y) := by
  induction h with
  | nil => simp at hlen
  | rel h => exact .rel h
  | cons h ih => exact .cons (ih (by simpa using hlen))

theorem shortlex_context {r : S → S → Prop} {u v : List S}
    (h : List.Shortlex r u v) (x y : List S) :
    List.Shortlex r (x++u++y) (x++v++y) := by
  simp only [List.append_assoc]
  apply List.Shortlex.append_left (s := x)
  rcases List.shortlex_def.mp h with h | ⟨hl,h⟩
  · apply List.Shortlex.of_length_lt
    simpa using h
  · exact List.Shortlex.of_lex (by simp [hl]) (lex_append_suffix h hl y)

theorem step_shortlex {r : S → S → Prop} {rules : List (List S × List S)}
    (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) {u v : List S}
    (h : Step rules u v) : List.Shortlex r v u := by
  cases h with
  | apply hm x y => exact shortlex_context (dec _ hm) x y

theorem steps_length {r : S → S → Prop} {rules : List (List S × List S)}
    (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) {u v : List S}
    (h : Steps rules u v) : v.length ≤ u.length := by
  induction h with
  | refl => rfl
  | tail huv hvw ih =>
    have hh := List.shortlex_def.mp (step_shortlex dec hvw)
    omega

theorem steps_wellFounded {r : S → S → Prop} {rules : List (List S × List S)}
    (wf : WellFounded r) (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) :
    WellFounded (flip (Step rules)) :=
  (List.Shortlex.wf wf).mono (fun _ _ h => step_shortlex dec h)

/-- A bounded table sees precisely those rules whose left sides fit the bound. -/
theorem step_stable {rs rt : List (List S × List S)} {k : ℕ}
    (stable : ∀ p, p.1.length ≤ k → (p ∈ rs ↔ p ∈ rt)) {w v : List S}
    (hw : w.length ≤ k) : Step rs w v ↔ Step rt w v := by
  constructor
  · intro h
    cases h with
    | apply hm x y =>
      apply Step.apply ((stable _ (by simp only [List.length_append] at hw; dsimp only; omega)).mp hm)
  · intro h
    cases h with
    | apply hm x y =>
      apply Step.apply ((stable _ (by simp only [List.length_append] at hw; dsimp only; omega)).mpr hm)

variable [DecidableEq S]

/-- The fixed choice of rule at the leftmost position, then table order. -/
def rootNext (w : List S) : List (List S × List S) → Option (List S)
  | [] => none
  | (u,v)::rs => if w.take u.length = u then some (v ++ w.drop u.length) else rootNext w rs

def next (rules : List (List S × List S)) : List S → Option (List S)
  | [] => rootNext [] rules
  | a::w => (rootNext (a::w) rules).or ((next rules w).map (a::·))

theorem rootNext_sound {w v : List S} {rules : List (List S × List S)}
    (h : rootNext w rules = some v) : ∃ u t, (u,t) ∈ rules ∧
      ∃ y, w = u++y ∧ v = t++y := by
  induction rules with
  | nil => simp [rootNext] at h
  | cons p rs ih =>
    rcases p with ⟨u,t⟩
    simp only [rootNext] at h
    split at h
    next he =>
      obtain rfl := Option.some.inj h
      exact ⟨u,t,List.mem_cons_self, w.drop u.length,
        by simpa only [he] using (List.take_append_drop u.length w).symm,rfl⟩
    next he =>
      obtain ⟨u,t,hm,y,hw,hv⟩ := ih h
      exact ⟨u,t,List.mem_cons_of_mem _ hm,y,hw,hv⟩

theorem rootNext_none {w : List S} {rules : List (List S × List S)}
    (h : rootNext w rules = none) {u t y : List S} (hm : (u,t) ∈ rules) : w ≠ u ++ y := by
  induction rules with
  | nil => simp at hm
  | cons p rs ih =>
    rcases p with ⟨a,b⟩
    simp only [rootNext] at h
    split at h
    · simp at h
    next he =>
      rcases List.mem_cons.mp hm with hp | hm
      · cases hp
        intro hw
        exact he (by simp [hw])
      · exact ih h hm

theorem next_sound {rules : List (List S × List S)} {w v : List S}
    (h : next rules w = some v) : Step rules w v := by
  induction w generalizing v with
  | nil =>
      obtain ⟨u,t,hm,y,hw,hv⟩ := rootNext_sound h
      have hh : Step rules (u++y) (t++y) := by
        simpa only [List.nil_append] using Step.apply hm [] y
      rw [← hw,← hv] at hh
      exact hh
  | cons a w ih =>
      simp only [next] at h
      cases hr : rootNext (a::w) rules with
      | some z =>
          simp [hr] at h
          subst z
          obtain ⟨u,t,hm,y,hw,hv⟩ := rootNext_sound hr
          have hh : Step rules (u++y) (t++y) := by
            simpa only [List.nil_append] using Step.apply hm [] y
          rw [← hw,← hv] at hh
          exact hh
      | none =>
          simp only [hr,Option.none_or,Option.map_eq_some_iff] at h
          obtain ⟨z,hz,rfl⟩ := h
          simpa only [List.singleton_append,List.append_nil] using step_context (ih hz) [a] []

theorem next_none_root {rules : List (List S × List S)} {w : List S}
    (h : next rules w = none) : rootNext w rules = none := by
  cases w with
  | nil => exact h
  | cons a w => exact (Option.or_eq_none_iff.mp h).1

theorem next_none_tail {rules : List (List S × List S)} {a : S} {w : List S}
    (h : next rules (a::w) = none) : next rules w = none := by
  exact Option.map_eq_none_iff.mp (Option.or_eq_none_iff.mp h).2

theorem next_none {rules : List (List S × List S)} {w : List S}
    (h : next rules w = none) : Irreducible (Step rules) w := by
  intro v hv
  cases hv with
  | @apply u t hm x y =>
    induction x with
    | nil => exact rootNext_none (next_none_root h) hm rfl
    | cons a x ih => exact ih (next_none_tail h)

/-- Fully specified finite-table reduction; divergence is retained for arbitrary
    (possibly nonterminating) tables. -/
def iteration (s : List (List S × List S) × List S) :
    List S ⊕ (List (List S × List S) × List S) :=
  match next s.1 s.2 with
  | none => .inl s.2
  | some v => .inr (s.1,v)

def evaluate (rules : List (List S × List S)) (w : List S) : Part (List S) :=
  PFun.fix (fun s => Part.some (iteration s)) (rules,w)

 theorem evaluate_sound {rules : List (List S × List S)} {w v : List S}
    (h : v ∈ evaluate rules w) : Steps rules w v ∧ Irreducible (Step rules) v := by
  change v ∈ PFun.fix _ (rules,w) at h
  refine PFun.fixInduction' (C := fun s => Steps s.1 s.2 v ∧ Irreducible (Step s.1) v) h ?_ ?_
  · rintro ⟨rs,a⟩ ha
    simp only [Part.mem_some_iff,iteration] at ha
    cases hn : next rs a with
    | none =>
      simp only [hn,Sum.inl.injEq] at ha
      subst a
      exact ⟨.refl,next_none hn⟩
    | some b => simp [hn] at ha
  · rintro ⟨rs,a⟩ ⟨rt,b⟩ _ hab ih
    simp only [Part.mem_some_iff,iteration] at hab
    cases hn : next rs a with
    | none => simp [hn] at hab
    | some c =>
      simp only [hn,Sum.inr.injEq,Prod.mk.injEq] at hab
      rcases hab with ⟨rfl,rfl⟩
      exact ⟨.head (next_sound hn) ih.1,ih.2⟩

theorem evaluate_total {rules : List (List S × List S)}
    (wf : WellFounded (flip (Step rules))) (w : List S) : (evaluate rules w).Dom := by
  induction w using wf.induction with
  | h w ih =>
    cases hn : next rules w with
    | none =>
      exact Part.dom_iff_mem.mpr ⟨w,PFun.fix_stop (by simp [iteration,hn])⟩
    | some v =>
      obtain ⟨z,hz⟩ := Part.dom_iff_mem.mp (ih v (next_sound hn))
      apply Part.dom_iff_mem.mpr
      refine ⟨z,PFun.mem_fix_iff.mpr (Or.inr ⟨(rules,v),?_,hz⟩)⟩
      simp [iteration,hn]

omit [DecidableEq S] in
/-- Bounded local confluence is enough: every intervening reduction has
    nonincreasing length, so no confluence outside the source budget is used. -/
theorem evaluate_unique_on {r : S → S → Prop} {rules : List (List S × List S)}
    (wf : WellFounded r) (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) (n : ℕ)
    (localJoin : ∀ a b c, a.length ≤ n → Step rules a b → Step rules a c →
      Join (Steps rules) b c) {a b c : List S} (ha : a.length ≤ n)
    (hab : Steps rules a b) (hac : Steps rules a c)
    (hb : Irreducible (Step rules) b) (hc : Irreducible (Step rules) c) : b = c := by
  induction a using (steps_wellFounded wf dec).induction generalizing b c with
  | h a ih =>
    rcases hab.cases_head with rfl | ⟨b₁,hab₁,hb₁b⟩
    · exact irreducible_reaches _ hb hac
    rcases hac.cases_head with rfl | ⟨c₁,hac₁,hc₁c⟩
    · exact (irreducible_reaches _ hc (.head hab₁ hb₁b)).symm
    obtain ⟨d,hb₁d,hc₁d⟩ := localJoin a b₁ c₁ ha hab₁ hac₁
    obtain ⟨e,hde,he⟩ := exists_irreducible _ (steps_wellFounded wf dec) d
    have hb₁ : b₁.length ≤ n := (steps_length dec (.single hab₁)).trans ha
    have hc₁ : c₁.length ≤ n := (steps_length dec (.single hac₁)).trans ha
    exact (ih b₁ hab₁ hb₁ hb₁b (hb₁d.trans hde) hb he).trans
      (ih c₁ hac₁ hc₁ hc₁c (hc₁d.trans hde) hc he).symm

theorem evaluate_context_on {r : S → S → Prop} {rules : List (List S × List S)}
    (wf : WellFounded r) (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) (n : ℕ)
    (localJoin : ∀ a b c, a.length ≤ n → Step rules a b → Step rules a c →
      Join (Steps rules) b c) {w v : List S} (hv : v ∈ evaluate rules w)
    (x y : List S) (hm : (x++w++y).length ≤ n) :
    evaluate rules (x++v++y) = evaluate rules (x++w++y) := by
  obtain ⟨a,ha⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf dec) (x++v++y))
  obtain ⟨b,hb⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf dec) (x++w++y))
  obtain ⟨hva,haI⟩ := evaluate_sound ha
  obtain ⟨hwb,hbI⟩ := evaluate_sound hb
  have hab := evaluate_unique_on wf dec n localJoin hm
    ((steps_context (evaluate_sound hv).1 x y).trans hva) hwb haI hbI
  subst b
  exact (Part.eq_some_iff.mpr ha).trans (Part.eq_some_iff.mpr hb).symm

variable [Primcodable S]

 theorem primrec_rootNext : Primrec₂ (@rootNext S _) := by
  apply Primrec₂.of_eq (Primrec.list_rec Primrec.snd (Primrec.const none)
    ((Primrec.ite
      (Primrec.eq.comp
        (Primrec.list_take.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.option_some.comp (Primrec.list_append.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_drop.comp
          (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂)).to₂
  intro w rs
  induction rs with
  | nil => rfl
  | cons p rs ih =>
      simpa [rootNext] using (congrArg
        (fun t => if w.take p.1.length = p.1 then some (p.2++w.drop p.1.length) else t) ih)

 theorem primrec_next : Primrec₂ (@next S _) := by
  have hor : Primrec₂ (Option.or : Option (List S) → Option (List S) → Option (List S)) :=
    Primrec.option_orElse.of_eq (by intro a b; cases a <;> rfl)
  apply Primrec₂.of_eq (Primrec.list_rec Primrec.snd
    (primrec_rootNext.comp (Primrec.const []) Primrec.fst)
    ((hor.comp
      (primrec_rootNext.comp
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        ((Primrec.list_cons.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂))).to₂)).to₂
  intro rs w
  induction w with
  | nil => rfl
  | cons a w ih =>
      simpa [next] using (congrArg
        (fun t => (rootNext (a::w) rs).or (t.map (a::·))) ih)

 theorem primrec_iteration : Primrec (@iteration S _) := by
  exact (Primrec.option_casesOn (primrec_next.comp Primrec.fst Primrec.snd)
    (Primrec.sumInl.comp Primrec.snd)
    ((Primrec.sumInr.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)).of_eq
    (by intro s; cases h : next s.1 s.2 <;> simp [iteration,h])

 theorem partrec_evaluate : Partrec₂ (@evaluate S _) :=
  Partrec.fix primrec_iteration.to_comp

end

/- The marker/constant-width code used in the self-reference construction.
   A block has its marker only at the start, not at the end. -/

structure BlockCode (A S : Type*) where
  marker : S
  tail : A → List S
  width : ℕ
  tail_length : ∀ a, (tail a).length = width
  tail_avoids : ∀ a, marker ∉ tail a
  injective : Function.Injective tail

namespace BlockCode
variable {A S : Type*} (C : BlockCode A S)

def block (a : A) : List S := C.marker :: C.tail a

def encode (w : List A) : List S := w.flatMap C.block

@[simp] theorem block_length (a : A) : (C.block a).length = C.width+1 := by
  simp [block,C.tail_length]

@[simp] theorem encode_nil : C.encode [] = [] := rfl
@[simp] theorem encode_cons (a : A) (w : List A) : C.encode (a::w) = C.block a ++ C.encode w := rfl
@[simp] theorem encode_append (u v : List A) : C.encode (u++v) = C.encode u ++ C.encode v := by
  simp [encode]
@[simp] theorem encode_length (w : List A) : (C.encode w).length = (C.width+1)*w.length := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih,Nat.mul_add,Nat.add_comm]

 theorem block_injective : Function.Injective C.block := by
  intro a b h
  exact C.injective (List.cons.inj h).2

 theorem prefix_decode {u v : List A} {y : List S} (h : C.encode v = C.encode u ++ y) :
    ∃ w, v = u++w ∧ y = C.encode w := by
  induction u generalizing v with
  | nil => exact ⟨v,rfl,h.symm⟩
  | cons a u ih =>
    cases v with
    | nil => simp [block] at h
    | cons b v =>
      simp only [encode_cons,List.append_assoc] at h
      obtain ⟨hab,ht⟩ := List.append_inj h (by simp)
      have : b=a := C.block_injective hab
      subst b
      obtain ⟨w,rfl,rfl⟩ := ih ht
      exact ⟨w,rfl,rfl⟩

 theorem encode_injective : Function.Injective C.encode := by
  intro u v h
  obtain ⟨w,hu,hw⟩ := C.prefix_decode (y := []) (by simpa using h)
  have he := congrArg List.length hw
  have : w=[] := by simpa using he
  simpa [this] using hu

 theorem split_past_avoiding {b : S} {t z x y : List S} (ht : b ∉ t)
    (h : t++z = x++b::y) : ∃ x', x=t++x' ∧ z=x'++b::y := by
  induction t generalizing x with
  | nil => exact ⟨x,rfl,h⟩
  | cons a t ih =>
    cases x with
    | nil =>
      have ha : a=b := (List.cons.inj h).1
      exact False.elim (ht (by simp [ha]))
    | cons c x =>
      obtain ⟨rfl,htail⟩ := List.cons.inj h
      obtain ⟨x',rfl,hz⟩ := ih (fun hh => ht (List.mem_cons_of_mem _ hh)) htail
      exact ⟨x',rfl,hz⟩

/-- Every marker inside an encoded word starts a complete generator block. -/
 theorem marker_alignment {v : List A} {x y : List S}
    (h : C.encode v = x ++ C.marker :: y) :
    ∃ u a w, v=u++a::w ∧ x=C.encode u ∧ y=C.tail a ++ C.encode w := by
  induction v generalizing x with
  | nil => simp at h
  | cons a v ih =>
    cases x with
    | nil =>
      have hy : C.tail a ++ C.encode v = y := (List.cons.inj h).2
      exact ⟨[],a,v,rfl,rfl,hy.symm⟩
    | cons b x =>
      obtain ⟨hb,hv⟩ := List.cons.inj h
      subst b
      obtain ⟨x',rfl,hv'⟩ := split_past_avoiding (C.tail_avoids a) hv
      obtain ⟨u,b,w,rfl,hx,hy⟩ := ih hv'
      exact ⟨a::u,b,w,rfl,by simp [block,hx],hy⟩

/-- A nonempty code occurrence in a code sequence has both boundaries aligned. -/
 theorem occurrence_decode {v u : List A} (hu : u≠[]) {x y : List S}
    (h : C.encode v = x++C.encode u++y) :
    ∃ p q, v=p++u++q ∧ x=C.encode p ∧ y=C.encode q := by
  cases u with
  | nil => contradiction
  | cons a u =>
    have hm : C.encode v = x++C.marker::(C.tail a++C.encode u++y) := by
      simpa [block,List.append_assoc] using h
    obtain ⟨p,b,w,hv,rfl,hy⟩ := C.marker_alignment hm
    have hh : C.encode (b::w) = C.encode (a::u)++y := by
      apply List.append_cancel_left (as := C.encode p)
      simpa only [hv,encode_append,List.append_assoc] using h
    obtain ⟨q,hq,hqy⟩ := C.prefix_decode hh
    refine ⟨p,q,?_,rfl,hqy⟩
    rw [hv,hq,List.append_assoc]

/-- Overlapping code left sides have a union which is itself a full code;
    the common part is an entire (nonempty) code suffix/prefix. -/
 theorem overlap_decode {u v : List A} {p middle q : List S}
    (hm : middle≠[]) (h₁ : C.encode u = p++middle)
    (h₂ : C.encode v = middle++q) :
    ∃ a b c, u=a++b ∧ v=b++c ∧ p=C.encode a ∧
      middle=C.encode b ∧ q=C.encode c := by
  cases v with
  | nil => simp at h₂; exact False.elim (hm h₂.1)
  | cons v vs =>
    cases middle with
    | nil => contradiction
    | cons m middle =>
      have hmark : m=C.marker := (List.cons.inj h₂).1.symm
      subst m
      obtain ⟨a,b,bs,hu,hp,ht⟩ := C.marker_alignment h₁
      have hs : C.marker::middle = C.encode (b::bs) := by simp [block,ht]
      have hv : C.encode (v::vs) = C.encode (b::bs)++q := by simpa [hs] using h₂
      obtain ⟨c,hv,hq⟩ := C.prefix_decode hv
      exact ⟨a,b::bs,c,hu,hv,hp,hs,hq⟩

 theorem encode_avoids {s : S} (hm : s≠C.marker) (ht : ∀ a, s∉C.tail a)
    (u : List A) : s ∉ C.encode u := by
  simp only [encode,List.mem_flatMap,block,List.mem_cons]
  rintro ⟨a,_,h | h⟩
  · exact hm h
  · exact ht a h

theorem lex_append_two {r : S → S → Prop} {u v : List S}
    (h : List.Lex r u v) (hlen : u.length=v.length) (x y : List S) :
    List.Lex r (u++x) (v++y) := by
  induction h with
  | nil => simp at hlen
  | rel hh => exact .rel hh
  | cons h ih => exact .cons (ih (by simpa using hlen))

/-- The chosen generator order is transported from the equal-width blocks. -/
theorem encode_lex {r : A → A → Prop} {s : S → S → Prop}
    (hblock : ∀ a b, r a b → List.Lex s (C.block a) (C.block b))
    {u v : List A} (h : List.Lex r u v) : List.Lex s (C.encode u) (C.encode v) := by
  induction h with
  | nil => exact List.Lex.nil
  | rel hh => exact lex_append_two (hblock _ _ hh) (by simp) _ _
  | @cons a u v hh ih => exact List.Lex.append_left s ih (C.block a)

theorem encode_shortlex {r : A → A → Prop} {s : S → S → Prop}
    (hblock : ∀ a b, r a b → List.Lex s (C.block a) (C.block b))
    {u v : List A} (h : List.Shortlex r u v) : List.Shortlex s (C.encode u) (C.encode v) := by
  rcases List.shortlex_def.mp h with hl | ⟨hl,hlex⟩
  · exact List.Shortlex.of_length_lt (by simpa using Nat.mul_lt_mul_of_pos_left hl (Nat.succ_pos C.width))
  · exact List.Shortlex.of_lex (by simp [hl]) (C.encode_lex hblock hlex)

end BlockCode

/-- An explicit computable constant-width binary tail family. Choosing the
    generator order by its lexicographic order implements the source convention.
    The generous width still obeys D₀>M=2, with no machine-size restriction. -/
def binaryTail {S : Type*} (a c : S) (m : ℕ) (i : Fin m) : List S :=
  List.replicate i.val a ++ c :: List.replicate (m+1-i.val) a

@[simp] theorem binaryTail_length {S : Type*} (a c : S) (m : ℕ) (i : Fin m) :
    (binaryTail a c m i).length=m+2 := by
  simp only [binaryTail,List.length_append,List.length_replicate,List.length_cons]
  have hi := i.isLt
  omega

theorem binaryTail_injective {S : Type*} [DecidableEq S] {a c : S} (hac : a≠c) (m : ℕ) :
    Function.Injective (binaryTail a c m) := by
  have hx (i : Fin m) : (binaryTail a c m i).idxOf c=i.val := by
    rw [binaryTail,List.idxOf_append_of_notMem (by simp [hac.symm])]
    simp
  intro i j he
  apply Fin.ext
  simpa only [hx] using congrArg (List.idxOf c) he

def binaryCode {S : Type*} [DecidableEq S] (b a c : S)
    (hba : b≠a) (hbc : b≠c) (hac : a≠c) (m : ℕ) : BlockCode (Fin m) S where
  marker := b
  tail := binaryTail a c m
  width := m+2
  tail_length := binaryTail_length a c m
  tail_avoids := by intro i; simp [binaryTail,hba,hbc]
  injective := binaryTail_injective hac m

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} (wf : WellFounded r)
variable (q : List A → Q)

/-- Exactly the bounded tested-class candidate set in the self-reference construction. -/
def candidates (w : List A) : Set (List A) := {v | v.length ≤ w.length ∧ q v=q w}

noncomputable def least (w : List A) : List A :=
  (List.Shortlex.wf wf).min (candidates q w) ⟨w,le_rfl,rfl⟩

theorem least_mem (w : List A) : least wf q w ∈ candidates q w :=
  (List.Shortlex.wf wf).min_mem _ _

theorem least_length (w : List A) : (least wf q w).length ≤ w.length :=
  (least_mem wf q w).1

theorem least_class (w : List A) : q (least wf q w)=q w := (least_mem wf q w).2

theorem least_min {w v : List A} (hv : v.length≤w.length) (hq : q v=q w) :
    ¬ List.Shortlex r v (least wf q w) :=
  (List.Shortlex.wf wf).not_lt_min (candidates q w) ⟨hv,hq⟩

theorem least_lt_or_eq [Std.Trichotomous r] (w : List A) :
    List.Shortlex r (least wf q w) w ∨ least wf q w=w := by
  have hh := Std.Trichotomous.trichotomous (r := List.Shortlex r) (least wf q w) w
  by_cases h : List.Shortlex r (least wf q w) w
  · exact Or.inl h
  · exact Or.inr (hh h (least_min wf q le_rfl rfl))

theorem least_global_min {w v : List A} (hq : q v=q w) : ¬ List.Shortlex r v (least wf q w) := by
  intro hd
  have hlen : v.length≤w.length := by
    have hm := least_length wf q w
    have he := List.shortlex_def.mp hd
    omega
  exact least_min wf q hlen hq hd

/-- Changing the finite search bound to that of another same-class candidate
    cannot change the result, including when the result is empty. -/
theorem least_congr [Std.Trichotomous r] {u v : List A} (hq : q u=q v) :
    least wf q u=least wf q v := by
  apply Std.Trichotomous.trichotomous (r := List.Shortlex r)
  · exact least_global_min wf q ((least_class wf q u).trans hq)
  · exact least_global_min wf q ((least_class wf q v).trans hq.symm)

theorem least_idem [Std.Trichotomous r] (w : List A) :
    least wf q (least wf q w)=least wf q w :=
  least_congr wf q (least_class wf q w)

theorem least_nil : least wf q []=[] := by
  have hh := least_length wf q []
  simpa using hh

/-- Literal characterization which requires no class tests longer than w. -/
theorem eq_least_iff [Std.Trichotomous r] {w v : List A} : v=least wf q w ↔
    v.length≤w.length ∧ q v=q w ∧
      ∀ t, t.length≤w.length → q t=q w → ¬ List.Shortlex r t v := by
  constructor
  · rintro rfl
    exact ⟨least_length wf q w,least_class wf q w,fun _ ht hq => least_min wf q ht hq⟩
  · rintro ⟨hv,hq,hm⟩
    exact Std.Trichotomous.trichotomous _ _
      (least_min wf q hv hq) (hm _ (least_length wf q w) (least_class wf q w))

end Canonical

open Relation
variable {S : Type*}

theorem step_mono {rs rt : List (List S × List S)} (h : ∀ p∈rs, p∈rt)
    {u v : List S} (huv : Step rs u v) : Step rt u v := by
  cases huv with
  | apply hp x y => exact .apply (h _ hp) x y

theorem steps_mono {rs rt : List (List S × List S)} (h : ∀ p∈rs, p∈rt)
    {u v : List S} (huv : Steps rs u v) : Steps rt u v := by
  induction huv with
  | refl => exact .refl
  | tail hh hs ih => exact .tail ih (step_mono h hs)

/-- The absorbing equations, stated as finite-table membership, not as an
    additional computation oracle. -/
def Absorbs (rs : List (List S × List S)) (z : S) : Prop :=
  ∀ a, ([z,a],[z])∈rs ∧ ([a,z],[z])∈rs

theorem absorbs_context {rs : List (List S × List S)} {z : S} (hz : Absorbs rs z)
    (x y : List S) : Steps rs (x++[z]++y) [z] := by
  have hr : ∀ y : List S, Steps rs ([z]++y) [z] := by
    intro y
    induction y with
    | nil => exact .refl
    | cons a y ih =>
      have hs : Steps rs ([z]++a::y) ([z]++y) :=
        .single (by simpa using Step.apply (hz a).1 [] y)
      exact hs.trans ih
  induction x with
  | nil => exact hr y
  | cons a x ih =>
    have hh := steps_context ih [a] []
    have hs : Step rs [a,z] [z] := by simpa using Step.apply (hz a).2 [] []
    have hh' : Steps rs (a::x++[z]++y) [a,z] := by simpa using hh
    exact hh'.trans (.single hs)

theorem absorbs_mem {rs : List (List S × List S)} {z : S} (hz : Absorbs rs z)
    {w : List S} (hw : z∈w) : Steps rs w [z] := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · exact absorbs_context hz [] w
    · have hh := steps_context (ih hw) [a] []
      have hh' : Steps rs (a::w) [a,z] := by simpa using hh
      exact hh'.trans (.single (by simpa using Step.apply (hz a).2 [] []))

theorem step_preserves_letter {rs : List (List S × List S)} {z : S}
    (hz : ∀ p∈rs, z∈p.1 → z∈p.2) {w v : List S} (hw : z∈w) (h : Step rs w v) : z∈v := by
  cases h with
  | apply hp x y =>
    simp only [List.mem_append] at hw ⊢
    rcases hw with (hx | hu) | hy
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr (hz _ hp hu))
    · exact Or.inr hy

namespace Static
variable {A Q : Type*} [Fintype A] [DecidableEq S]
variable {r : A → A → Prop}
variable (C : BlockCode A S) (wf : WellFounded r) (q : List A → Option Q) (z : S)

noncomputable def letters (A : Type*) [Fintype A] : List A := (Finset.univ : Finset A).toList
noncomputable def words (A : Type*) [Fintype A] : ℕ → List (List A)
  | 0 => [[]]
  | n+1 => [] :: (letters A).flatMap (fun a => (words A n).map (a::·))

@[simp] theorem mem_words (n : ℕ) (w : List A) : w∈words A n ↔ w.length≤n := by
  classical
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w => simp [words,letters,ih]

noncomputable def output (v : List A) : List S :=
  if q v=none then [z] else C.encode (Canonical.least wf q v)

noncomputable def table (n : ℕ) : List (List S × List S) :=
  ((words A n).filter fun v => v≠[] ∧ output C wf q z v≠C.encode v).map
    (fun v => (C.encode v,output C wf q z v))

theorem mem_table {n : ℕ} {a b : List S} : (a,b)∈table C wf q z n ↔
    ∃ v, v.length≤n ∧ v≠[] ∧ output C wf q z v≠C.encode v ∧
      a=C.encode v ∧ b=output C wf q z v := by
  simp only [table,List.mem_map,List.mem_filter,mem_words,decide_eq_true_eq,Prod.mk.injEq]
  aesop

omit [Fintype A] [DecidableEq S] in
theorem output_congr [Std.Trichotomous r] {u v : List A} (hq : q u=q v) :
    output C wf q z u=output C wf q z v := by
  simp only [output,hq,Canonical.least_congr wf q hq]

omit [Fintype A] [DecidableEq S] in
theorem output_nil (hzero : q []≠none) : output C wf q z []=[] := by
  simp [output,hzero,Canonical.least_nil]

theorem whole_steps (hzero : q []≠none) {n : ℕ} {v : List A} (hv : v.length≤n) :
    Steps (table C wf q z n) (C.encode v) (output C wf q z v) := by
  by_cases hn : v=[]
  · subst v
    rw [C.encode_nil,output_nil C wf q z hzero]
  by_cases he : output C wf q z v=C.encode v
  · rw [he]
  · exact .single (by simpa using Step.apply ((mem_table C wf q z).mpr ⟨v,hv,hn,he,rfl,rfl⟩) [] [])

/-- Precisely the bounded contextual tests used at source bootstrap:273–297. -/
def Contextual (n : ℕ) : Prop :=
  ∀ a b u v : List A, (a++u++b).length≤n → (a++v++b).length≤n → q u=q v →
    q (a++u++b)=q (a++v++b)

def ZeroIdeal (n : ℕ) : Prop :=
  ∀ a b u : List A, (a++u++b).length≤n → q u=none → q (a++u++b)=none

variable [Std.Trichotomous r]

/-- A single contextual static replacement inside a full code reduces to the
    same literal whole-code output. Both endpoint bounds are proved separately. -/
theorem branch_normalizes {n : ℕ} {rs : List (List S × List S)}
    (hzero : q []≠none) (hz : Absorbs rs z)
    (ht : ∀ p∈table C wf q z n, p∈rs)
    (hc : Contextual q n) (hi : ZeroIdeal q n)
    {v : List A} {a b : List A} (hlen : (a++v++b).length≤n) :
    Steps rs (C.encode a++output C wf q z v++C.encode b) (output C wf q z (a++v++b)) := by
  by_cases hq : q v=none
  · have hzq := hi a b v hlen hq
    simp only [output,ite_eq_left hq,ite_eq_left hzq]
    exact absorbs_context hz _ _
  · let v' := Canonical.least wf q v
    have hlen' : (a++v'++b).length≤n := by
      have hh := Canonical.least_length wf q v
      simp only [List.length_append] at hlen ⊢
      dsimp only [v']
      omega
    have hqq : q (a++v'++b)=q (a++v++b) :=
      hc a b v' v hlen' hlen (Canonical.least_class wf q v)
    have hh := steps_mono ht (whole_steps C wf q z hzero hlen')
    rw [output_congr C wf q z hqq] at hh
    simpa only [output,ite_eq_right hq,BlockCode.encode_append,v'] using hh

/-- Contained code occurrences are aligned, so the preceding branch analysis
    applies at exactly the source code boundaries. -/
theorem occurrence_normalizes {n : ℕ} {rs : List (List S × List S)}
    (hzero : q []≠none) (hz : Absorbs rs z)
    (ht : ∀ p∈table C wf q z n, p∈rs)
    (hc : Contextual q n) (hi : ZeroIdeal q n)
    {w v : List A} {x y : List S} (hw : w.length≤n) (hv : v≠[])
    (he : C.encode w=x++C.encode v++y) :
    Steps rs (x++output C wf q z v++y) (output C wf q z w) := by
  obtain ⟨a,b,rfl,rfl,rfl⟩ := C.occurrence_decode hv he
  exact branch_normalizes C wf q z hzero hz ht hc hi hw

/-- Static containment criticals join at the canonical output of the union. -/
theorem critical_containment {n k l : ℕ} {rs : List (List S × List S)}
    (hzero : q []≠none) (hz : Absorbs rs z)
    (ht : ∀ p∈table C wf q z n, p∈rs)
    (hc : Contextual q n) (hi : ZeroIdeal q n)
    {u u' v v' x y : List S}
    (hu : (u,u')∈table C wf q z k) (hv : (v,v')∈table C wf q z l)
    (he : u=x++v++y) (hlen : u.length≤(C.width+1)*n) :
    Join (Steps rs) u' (x++v'++y) := by
  obtain ⟨a,_,_,_,rfl,rfl⟩ := (mem_table C wf q z).mp hu
  obtain ⟨b,_,hbn,_,rfl,rfl⟩ := (mem_table C wf q z).mp hv
  have ha : a.length≤n := by
    rw [C.encode_length] at hlen
    exact Nat.le_of_mul_le_mul_left hlen (by omega)
  exact ⟨output C wf q z a,.refl,
    occurrence_normalizes C wf q z hzero hz ht hc hi ha hbn he⟩

/-- Static boundary criticals have a full, aligned code union, and both
    contextual branches reach its same literal output. -/
theorem critical_overlap {n k l : ℕ} {rs : List (List S × List S)}
    (hzero : q []≠none) (hz : Absorbs rs z)
    (ht : ∀ p∈table C wf q z n, p∈rs)
    (hc : Contextual q n) (hi : ZeroIdeal q n)
    {u u' v v' x middle y : List S}
    (hu : (u,u')∈table C wf q z k) (hv : (v,v')∈table C wf q z l)
    (hm : middle≠[]) (he : u=x++middle) (hf : v=middle++y)
    (hlen : (x++middle++y).length≤(C.width+1)*n) :
    Join (Steps rs) (u'++y) (x++v') := by
  obtain ⟨a,_,_,_,rfl,rfl⟩ := (mem_table C wf q z).mp hu
  obtain ⟨b,_,_,_,rfl,rfl⟩ := (mem_table C wf q z).mp hv
  obtain ⟨c,d,e,rfl,rfl,rfl,rfl,rfl⟩ := C.overlap_decode hm he hf
  have hlen' : (c++d++e).length≤n := by
    have hh : (C.encode (c++d++e)).length≤(C.width+1)*n := by
      simpa only [BlockCode.encode_append] using hlen
    rw [C.encode_length] at hh
    exact Nat.le_of_mul_le_mul_left hh (by omega)
  refine ⟨output C wf q z (c++d++e),?_,?_⟩
  · simpa only [List.nil_append,BlockCode.encode_nil] using
      branch_normalizes C wf q z hzero hz ht hc hi (a := []) (v := c++d) (b := e)
        (by simpa only [List.nil_append] using hlen')
  · simpa only [List.append_nil,BlockCode.encode_nil,List.append_assoc] using
      branch_normalizes C wf q z hzero hz ht hc hi (a := c) (v := d++e) (b := [])
        (by simpa only [List.append_nil,List.append_assoc] using hlen')

end Static
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI

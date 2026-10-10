import OAI.Computability.FiniteCompiler.Normalization

namespace OAI

/-!
Primitive recursive encodings and effective finite compiler data.
-/

/- Effectivity dependencies for the source compiler and its bounded recursive
   evaluator. No partial function is completed by classical choice. -/
namespace FiniteAlgebraicEnvelopes.Effect
variable {α β : Type*}

def traverse (f : α →. β) : List α →. List β
  | [] => Part.some []
  | a::l => (f a).bind fun b => (traverse f l).map (b::·)

def traverseStep (f : α →. β) : List α × List β →. List β ⊕ (List α × List β)
  | ([],acc) => Part.some (.inl acc)
  | (a::l,acc) => (f a).map fun b => .inr (l,acc++[b])

theorem traverse_fix (f : α →. β) (l : List α) (acc : List β) :
    PFun.fix (traverseStep f) (l,acc) = (traverse f l).map (acc++·) := by
  induction l generalizing acc with
  | nil =>
    apply Part.ext
    intro out
    rw [PFun.mem_fix_iff]
    simp [traverseStep,traverse]
  | cons a l ih =>
    apply Part.ext
    intro out
    rw [PFun.mem_fix_iff]
    simp only [traverseStep,Part.mem_map_iff,Sum.inr.injEq,
      Sum.inr_ne_inl,exists_false,and_false,false_or]
    constructor
    · rintro ⟨⟨l',acc'⟩,⟨b,hb,he⟩,h⟩
      rcases he with ⟨rfl,rfl⟩
      rw [ih] at h
      rcases (Part.mem_map_iff _).mp h with ⟨bs,hbs,rfl⟩
      refine ⟨b::bs,Part.mem_bind_iff.mpr ⟨b,hb,(Part.mem_map_iff _).mpr ⟨bs,hbs,rfl⟩⟩,?_⟩
      simp [List.append_assoc]
    · intro h
      rcases h with ⟨bs,hbs,rfl⟩
      change bs ∈ (f a).bind (fun b => (traverse f l).map (b::·)) at hbs
      rcases Part.mem_bind_iff.mp hbs with ⟨b,hb,hrest⟩
      rcases (Part.mem_map_iff _).mp hrest with ⟨tail,htail,rfl⟩
      refine ⟨(l,acc++[b]),⟨b,hb,rfl⟩,?_⟩
      rw [ih]
      apply (Part.mem_map_iff _).mpr
      exact ⟨tail,htail,by simp [List.append_assoc]⟩

variable [Primcodable α] [Primcodable β]

theorem partrec_traverse {f : α →. β} (hf : Partrec f) : Partrec (traverse f) := by
  have hs : Partrec (traverseStep f) := by
    have ht : Computable (fun s : List α × List β => s.1.head?) :=
      Primrec.list_head?.to_comp.comp Computable.fst
    have hb : Partrec₂ (fun (s : List α × List β) (a : α) =>
        (f a).map fun b => (Sum.inr (s.1.tail,s.2++[b]) : List β ⊕ (List α × List β))) := by
      change Partrec (fun sa : (List α × List β) × α =>
        (f sa.2).map fun b => (Sum.inr (sa.1.1.tail,sa.1.2++[b]) : List β ⊕ (List α × List β)))
      apply (hf.comp Computable.snd).map
      exact (Computable.sumInr.comp
        ((Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
        (Primrec.list_append.to_comp.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst))
          (Primrec.list_cons.to_comp.comp Computable.snd (Computable.const []))))).to₂
    exact (Partrec.optionCasesOn_right ht
      (Computable.sumInl.comp Computable.snd) hb).of_eq
      (by intro s; rcases s with ⟨l,acc⟩; cases l <;> rfl)
  exact ((Partrec.fix hs).comp (Computable.id.pair (Computable.const []))).of_eq fun l => by
    simpa only [id_eq,List.nil_append,Part.map_id' (fun _ => rfl)] using traverse_fix f l []

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

def Action.code : Action C S ≃ C ⊕ (List S ⊕ List S) where
  toFun
    | .keep c => .inl c
    | .raw x => .inr (.inl x)
    | .call x => .inr (.inr x)
  invFun
    | .inl c => .keep c
    | .inr (.inl x) => .raw x
    | .inr (.inr x) => .call x
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with c | (x|x) <;> rfl

instance [Primcodable C] [Primcodable S] : Primcodable (Action C S) :=
  Primcodable.ofEquiv _ Action.code

def push : Item C S → List (Action C S) → List (Action C S)
  | .inl c,p => .keep c::p
  | .inr x,[] => [.raw x]
  | .inr x,.keep c::p => .raw x::.keep c::p
  | .inr x,.raw y::p => .call (x++y)::p
  | .inr x,.call y::p => .call (x++y)::p

theorem plan_cons (a : Item C S) (w : List (Item C S)) :
    plan (a::w) = push a (plan w) := by
  cases a with
  | inl c => simp only [plan,push]
  | inr x =>
    cases w with
    | nil => simp [plan,splitRun,push]
    | cons b w =>
      cases b with
      | inl c => simp [plan,splitRun,push]
      | inr y =>
        rw [plan,plan]
        simp only [splitRun]
        cases (splitRun w).1 <;> simp [push]

theorem plan_fold (w : List (Item C S)) : plan w = w.foldr push [] := by
  induction w with
  | nil => simp [plan]
  | cons a w ih => rw [plan_cons,ih]; rfl

variable [Primcodable C] [Primcodable S]

 theorem Action.primrec_code : Primrec (Action.code (C := C) (S := S)) := Primrec.of_equiv
 theorem Action.primrec_decode : Primrec (Action.code (C := C) (S := S)).symm := Primrec.of_equiv_symm
 theorem Action.primrec_keep : Primrec (Action.keep (C := C) (S := S)) :=
  (Action.primrec_decode.comp Primrec.sumInl).of_eq fun _ => rfl
 theorem Action.primrec_raw : Primrec (Action.raw (C := C) (S := S)) :=
  (Action.primrec_decode.comp (Primrec.sumInr.comp Primrec.sumInl)).of_eq fun _ => rfl
 theorem Action.primrec_call : Primrec (Action.call (C := C) (S := S)) :=
  (Action.primrec_decode.comp (Primrec.sumInr.comp Primrec.sumInr)).of_eq fun _ => rfl

 theorem Action.primrec_cases {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → Action C S} {k : α → C → β} {r t : α → List S → β}
    (hf : Primrec f) (hk : Primrec₂ k) (hr : Primrec₂ r) (ht : Primrec₂ t) :
    Primrec (fun a => match f a with | .keep c => k a c | .raw x => r a x | .call x => t a x) := by
  have hh : Primrec₂ (fun a (b : List S ⊕ List S) => b.elim (r a) (t a)) :=
    (Primrec.sumCasesOn Primrec.snd
      (hr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (ht.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn (Action.primrec_code.comp hf) hk hh).of_eq fun a => by
    cases f a <;> rfl

 theorem primrec_push : Primrec₂ (push (C := C) (S := S)) := by
  have hl : Primrec₂ (fun (p : Item C S × List (Action C S)) (c : C) => Action.keep c::p.2) :=
    (Primrec.list_cons.comp (Action.primrec_keep.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have hr : Primrec₂ (fun (p : Item C S × List (Action C S)) (x : List S) =>
      match p.2 with
      | [] => [Action.raw x]
      | .keep c::l => Action.raw x::.keep c::l
      | .raw y::l => Action.call (x++y)::l
      | .call y::l => Action.call (x++y)::l) := by
    have hc : Primrec₂ (fun (p : (Item C S × List (Action C S)) × List S)
        (q : Action C S × List (Action C S)) =>
        match q.1 with
        | .keep c => Action.raw p.2::.keep c::q.2
        | .raw y => Action.call (p.2++y)::q.2
        | .call y => Action.call (p.2++y)::q.2) := by
      exact (Action.primrec_cases (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp
          (Action.primrec_raw.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.list_cons.comp (Action.primrec_keep.comp Primrec.snd)
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to₂
        (Primrec.list_cons.comp
          (Action.primrec_call.comp (Primrec.list_append.comp
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
        (Primrec.list_cons.comp
          (Action.primrec_call.comp (Primrec.list_append.comp
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂).to₂
    exact (Primrec.list_casesOn (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp (Action.primrec_raw.comp Primrec.snd) (Primrec.const [])) hc).to₂.of_eq
      (by intro p x; cases p.2 with
        | nil => rfl
        | cons a l => cases a <;> rfl)
  exact (Primrec.sumCasesOn Primrec.fst hl hr).to₂.of_eq fun a p => by
    cases a with
    | inl c => rfl
    | inr x => cases p with
      | nil => rfl
      | cons a p => cases a <;> rfl

 theorem primrec_plan : Primrec (plan (C := C) (S := S)) :=
  (Primrec.list_foldr Primrec.id (Primrec.const [])
    (primrec_push.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun w => (plan_fold w).symm)

 theorem Action.partrec_partial {f : List S →. List S} (hf : Partrec f) :
    Partrec (Action.partial (C := C) f) := by
  have hh : Partrec₂ (fun (_ : Action C S) (b : List S ⊕ List S) =>
      b.elim (fun x => Part.some (Sum.inr x : Item C S)) (fun x => (f x).map (Sum.inr (α := C)))) := by
    exact (Partrec.sumCasesOn_right Computable.snd
      (Computable.sumInr.comp Computable.snd).to₂
      (((hf.comp Computable.snd).map (Computable.sumInr.comp Computable.snd).to₂).to₂)).to₂
  exact (Partrec.sumCasesOn_right Action.primrec_code.to_comp
    (Computable.sumInl.comp Computable.snd).to₂ hh).of_eq fun a => by
      cases a <;> rfl

 theorem partrec_execute {f : List S →. List S} (hf : Partrec f) :
    Partrec (execute (C := C) f) := by
  apply (Effect.partrec_traverse (Action.partrec_partial hf)).of_eq
  intro p
  induction p with
  | nil => rfl
  | cons a p ih => simp only [Effect.traverse,execute,ih]

 theorem partrec_partialSource {f : List S →. List S} (hf : Partrec f) :
    Partrec (partialSource (C := C) f) :=
  (partrec_execute hf).comp primrec_plan.to_comp

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Effect.Graph
open Relation
variable {α : Type*} [DecidableEq α]

def expand (r : α → α → Bool) (u s : List α) : List α :=
  s ++ u.filter (fun b => s.any (fun a => r a b || r b a))

def search (r : α → α → Bool) (u : List α) (a : α) : ℕ → List α
  | 0 => [a]
  | n+1 => expand r u (search r u a n)

omit [DecidableEq α] in
@[simp] theorem mem_expand (r : α → α → Bool) (u s : List α) (b : α) :
    b ∈ expand r u s ↔ b ∈ s ∨ b ∈ u ∧ ∃ a ∈ s, r a b = true ∨ r b a = true := by
  simp [expand]

omit [DecidableEq α] in
theorem search_sub (r : α → α → Bool) {u : List α} {a : α} (ha : a ∈ u) (n : ℕ) :
    ∀ b ∈ search r u a n, b ∈ u := by
  induction n with
  | zero => simpa [search] using ha
  | succ n ih =>
    intro b hb
    rcases (mem_expand r u _ b).mp hb with hb | ⟨hb,_⟩
    · exact ih b hb
    · exact hb

theorem search_mono (r : α → α → Bool) (u : List α) (a : α) :
    Monotone (fun n => (search r u a n).toFinset) := by
  apply monotone_nat_of_le_succ
  intro n b hb
  simp only [List.mem_toFinset] at hb ⊢
  exact (mem_expand r u _ b).mpr (Or.inl hb)

theorem expand_ext (r : α → α → Bool) (u : List α) {s t : List α}
    (h : s.toFinset = t.toFinset) : (expand r u s).toFinset = (expand r u t).toFinset := by
  have hh : ∀ a, a ∈ s ↔ a ∈ t := fun a => by
    simpa only [List.mem_toFinset] using Finset.ext_iff.mp h a
  ext b
  simp only [List.mem_toFinset,mem_expand,hh]

theorem search_stable (r : α → α → Bool) {u : List α} {a : α} (ha : a ∈ u) :
    (search r u a (u.length+1)).toFinset = (search r u a u.length).toFinset := by
  have hs : ∀ n, (search r u a n).toFinset.card ≤ u.length := by
    intro n
    exact (Finset.card_le_card (fun b hb => by
      simp only [List.mem_toFinset] at hb ⊢
      exact search_sub r ha n b hb)).trans (List.toFinset_card_le u)
  have hm : Monotone (fun n => (search r u a n).toFinset.card) :=
    fun _ _ h => Finset.card_le_card (search_mono r u a h)
  have hstep : ∀ n, (search r u a n).toFinset.card = (search r u a (n+1)).toFinset.card →
      (search r u a (n+1)).toFinset.card = (search r u a (n+2)).toFinset.card := by
    intro n hn
    have he := Finset.eq_of_subset_of_card_le (search_mono r u a (Nat.le_succ n)) hn.ge
    exact congrArg Finset.card (expand_ext r u he)
  exact (Finset.eq_of_subset_of_card_le
    (search_mono r u a (Nat.le_succ u.length))
    (Nat.stabilises_of_monotone hm hs hstep (Nat.le_succ _)).le).symm

def component (r : α → α → Bool) (u : List α) (a : α) : List α := search r u a u.length

omit [DecidableEq α] in
theorem mem_search_connected (r : α → α → Bool) (u : List α) (a : α) (n : ℕ)
    {b : α} (hb : b ∈ search r u a n) : EqvGen (fun a b => r a b = true) a b := by
  induction n generalizing b with
  | zero =>
    have : b = a := by simpa [search] using hb
    subst b
    exact .refl _
  | succ n ih =>
    rcases (mem_expand r u _ b).mp hb with hb | ⟨_,c,hc,hcb | hbc⟩
    · exact ih hb
    · exact .trans _ _ _ (ih hc) (.rel _ _ hcb)
    · exact .trans _ _ _ (ih hc) (.symm _ _ (.rel _ _ hbc))

theorem mem_component_iff (r : α → α → Bool) {u : List α} {a b : α} (ha : a ∈ u)
    (hclosed : ∀ c ∈ u, ∀ d, (r c d = true ∨ r d c = true) → d ∈ u) :
    b ∈ component r u a ↔ EqvGen (fun a b => r a b = true) a b := by
  constructor
  · exact mem_search_connected r u a u.length
  · intro h
    have hh : ReflTransGen (SymmGen (fun a b => r a b = true)) a b := by
      rw [EqvGen.reflTransGen_symmGen]; exact h
    clear h
    induction hh with
    | refl =>
      have := search_mono r u a (Nat.zero_le u.length)
        (show a ∈ (search r u a 0).toFinset by simp [search])
      simpa only [List.mem_toFinset,component] using this
    | @tail c d hp hs ih =>
      have hc := search_sub r ha u.length c ih
      have hed : r c d = true ∨ r d c = true := hs
      have hd := hclosed c hc d hed
      have hm := (mem_expand r u _ d).mpr (Or.inr ⟨hd,c,ih,hed⟩)
      have he : d ∈ (search r u a (u.length+1)).toFinset := List.mem_toFinset.mpr hm
      rw [search_stable r ha] at he
      exact List.mem_toFinset.mp he

variable [Primcodable α]

omit [DecidableEq α] in
 theorem primrec_listAny {β : Type*} [Primcodable β]
    {f : β → List α} {p : β → α → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun b => (f b).any (p b)) := by
  exact (Primrec.list_foldr hf (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun b => by
    induction f b <;> simp_all

omit [DecidableEq α] in
 theorem primrec_listFilter {β : Type*} [Primcodable β]
    {f : β → List α} {p : β → α → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun b => (f b).filter (p b)) := by
  exact (Primrec.listFilterMap hf
    (Primrec.cond hp (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂).of_eq
    fun b => by
      simp only [Bool.cond_eq_ite]
      induction f b with
      | nil => rfl
      | cons a l ih => cases h : p b a <;> simp [h,ih]

omit [DecidableEq α] in
 theorem primrec_expand {r : α → α → Bool} (hr : Primrec₂ r) :
    Primrec₂ (fun u s : List α => expand r u s) := by
  change Primrec (fun p : List α × List α => p.2 ++ p.1.filter
    (fun b => p.2.any (fun a => r a b || r b a)))
  apply Primrec.list_append.comp Primrec.snd
  apply primrec_listFilter Primrec.fst
  have hp : Primrec₂ (fun (p : (List α × List α) × α) (a : α) => r a p.2 || r p.2 a) :=
    (Primrec.or.comp (hr.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (hr.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
  exact (primrec_listAny (Primrec.snd.comp Primrec.fst) hp).to₂

omit [DecidableEq α] in
 theorem primrec_search {r : α → α → Bool} (hr : Primrec₂ r) :
    Primrec (fun p : (List α × α) × ℕ => search r p.1.1 p.1.2 p.2) := by
  change Primrec₂ (fun (p : List α × α) (n : ℕ) => search r p.1 p.2 n)
  exact (Primrec.nat_rec
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    ((primrec_expand hr).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      fun p n => by induction n <;> simp_all [search]

omit [DecidableEq α] in
 theorem primrec_component {r : α → α → Bool} (hr : Primrec₂ r) :
    Primrec₂ (component r) :=
  ((primrec_search hr).comp
    (Primrec.id.pair (Primrec.list_length.comp Primrec.fst))).to₂

end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

def Sector.code : Sector H B T ≃ List (B×T) × (H × (List (B×T) × (Bool × Bool))) where
  toFun v := (v.left,v.head,v.right,v.leftBoundary,v.rightBoundary)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Primcodable H] [Primcodable B] [Primcodable T] : Primcodable (Sector H B T) :=
  Primcodable.ofEquiv _ Sector.code

variable [Primcodable H] [Primcodable B] [Primcodable T]

theorem Sector.primrec_code : Primrec (Sector.code (H := H) (B := B) (T := T)) := Primrec.of_equiv
theorem Sector.primrec_decode : Primrec (Sector.code (H := H) (B := B) (T := T)).symm :=
  Primrec.of_equiv_symm

theorem Sector.primrec_left : Primrec (Sector.left (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp Sector.primrec_code
theorem Sector.primrec_head : Primrec (Sector.head (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp Sector.primrec_code)
theorem Sector.primrec_right : Primrec (Sector.right (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code))
theorem Sector.primrec_lb : Primrec (Sector.leftBoundary (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))
theorem Sector.primrec_rb : Primrec (Sector.rightBoundary (Head := H) (Base := B) (Tag := T)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))

theorem Sector.primrec_mk {α : Type*} [Primcodable α]
    {l r : α → List (B×T)} {q : α → H} {a b : α → Bool}
    (hl : Primrec l) (hq : Primrec q) (hr : Primrec r) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => (⟨l x,q x,r x,a x,b x⟩ : Sector H B T)) :=
  Sector.primrec_decode.comp (hl.pair (hq.pair (hr.pair (ha.pair hb))))

theorem primrec_baseSkeleton : Primrec (baseSkeleton (H := H) (B := B) (T := T)) :=
  (Primrec.list_map
    (Primrec.list_append.comp (Primrec.list_reverse.comp Sector.primrec_left) Sector.primrec_right)
    (Primrec.fst.comp Primrec.snd).to₂).pair (Sector.primrec_lb.pair Sector.primrec_rb)

variable [Fintype H] [Fintype B] [Fintype T]

-- All finite choices below are literal lists. No finset or finite-connectivity
-- decision is used as a computability oracle.
noncomputable def finiteList (α : Type*) [Fintype α] : List α := (Finset.univ : Finset α).toList

@[simp] theorem mem_finiteList {α : Type*} [Fintype α] (a : α) : a ∈ finiteList α := by
  classical
  simp [finiteList]

noncomputable def wordList (α : Type*) [Fintype α] : ℕ → List (List α)
  | 0 => [[]]
  | n+1 => [] :: (finiteList α).flatMap (fun a => (wordList α n).map (a::·))

@[simp] theorem mem_wordList {α : Type*} [Fintype α] (n : ℕ) (w : List α) :
    w ∈ wordList α n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordList]
  | succ n ih =>
    cases w with
    | nil => simp [wordList]
    | cons a w => simp [wordList,ih]

 theorem primrec_wordList {α : Type*} [Fintype α] [Primcodable α] : Primrec (wordList α) := by
  exact (Primrec.nat_rec₁ [[]]
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap (Primrec.const (finiteList α))
        (Primrec.list_map (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
    fun n => by induction n <;> simp_all [wordList]

noncomputable def sectorList (n : ℕ) : List (Sector H B T) :=
  (finiteList H).flatMap fun q =>
    (wordList (B×T) n).flatMap fun l =>
      (wordList (B×T) n).flatMap fun r =>
        [⟨l,q,r,false,false⟩,⟨l,q,r,false,true⟩,⟨l,q,r,true,false⟩,⟨l,q,r,true,true⟩]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_sectorList (n : ℕ) (v : Sector H B T) :
    v ∈ sectorList n ↔ v.left.length ≤ n ∧ v.right.length ≤ n := by
  rcases v with ⟨l,q,r,a,b⟩
  cases a <;> cases b <;> simp [sectorList,Sector.mk.injEq]

 theorem primrec_sectorList : Primrec (sectorList (H := H) (B := B) (T := T)) := by
  apply Primrec.list_flatMap (Primrec.const (finiteList H))
  unfold Primrec₂
  apply Primrec.list_flatMap (primrec_wordList.comp Primrec.fst)
  unfold Primrec₂
  apply Primrec.list_flatMap (primrec_wordList.comp (Primrec.fst.comp Primrec.fst))
  unfold Primrec₂
  have hm (a b : Bool) : Primrec (fun p : ((ℕ × H) × List (B×T)) × List (B×T) =>
      (⟨p.1.2,p.1.1.2,p.2,a,b⟩ : Sector H B T)) :=
    Sector.primrec_mk (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
      (Primrec.const a) (Primrec.const b)
  exact Primrec.list_cons.comp (hm false false)
    (Primrec.list_cons.comp (hm false true)
      (Primrec.list_cons.comp (hm true false)
        (Primrec.list_cons.comp (hm true true) (Primrec.const []))))

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

noncomputable def universeList (v : Sector H B T) : List (Sector H B T) :=
  (sectorList (v.left.length+v.right.length)).filter fun w => baseSkeleton w = baseSkeleton v

omit [Primcodable H] [Primcodable B] [Primcodable T] [DecidableEq H] [DecidableEq T] in
@[simp] theorem mem_universeList (v w : Sector H B T) :
    w ∈ universeList v ↔ baseSkeleton w = baseSkeleton v := by
  simp only [universeList,List.mem_filter,mem_sectorList,decide_eq_true_eq,and_iff_right_iff_imp]
  intro h
  have hl := skeleton_length h
  constructor <;> omega

omit [DecidableEq H] [DecidableEq T] in
 theorem primrec_universeList : Primrec (universeList (H := H) (B := B) (T := T)) := by
  apply primrec_listFilter
    (primrec_sectorList.comp (Primrec.nat_add.comp
      (Primrec.list_length.comp Sector.primrec_left) (Primrec.list_length.comp Sector.primrec_right)))
  exact (Primrec.eq.decide.comp (primrec_baseSkeleton.comp Primrec.snd)
    (primrec_baseSkeleton.comp Primrec.fst)).to₂

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
variable {H T : Type*}

def Instruction.code : Instruction H T ≃ H × T × Bool where
  toFun i := (i.head,i.tag,i.cross)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Primcodable H] [Primcodable T] : Primcodable (Instruction H T) :=
  Primcodable.ofEquiv _ Instruction.code

theorem Instruction.primrec_head [Primcodable H] [Primcodable T] :
    Primrec (Instruction.head (Head := H) (Tag := T)) := Primrec.fst.comp Primrec.of_equiv

theorem Instruction.primrec_tag [Primcodable H] [Primcodable T] :
    Primrec (Instruction.tag (Head := H) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.of_equiv)

theorem Instruction.primrec_cross [Primcodable H] [Primcodable T] :
    Primrec (Instruction.cross (Head := H) (Tag := T)) :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv)
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

def flip (v : Sector H B T) : Sector H B T :=
  ⟨v.right,v.head,v.left,v.rightBoundary,v.leftBoundary⟩

def rightStep (table : Table H B T) (v : Sector H B T) : Option (Sector H B T) :=
  match v.right with
  | [] => if v.rightBoundary then (table.boundary v.head).map fun q => {v with head := q} else none
  | (b,t)::r => (table.cell v.head b t).map fun a =>
      if a.cross then {v with left := (b,a.tag)::v.left,head := a.head,right := r}
      else {v with head := a.head,right := (b,a.tag)::r}

theorem step_rightStep (table : Table H B T) (v : Sector H B T) :
    step table v = if table.direction v.head = .right then rightStep table v
      else (rightStep table (flip v)).map flip := by
  rcases v with ⟨l,q,r,a,b⟩
  cases hd : table.direction q with
  | right =>
    cases r with
    | nil => simp [step,rightStep,hd]
    | cons c r => cases c; simp [step,rightStep,hd]
  | left =>
    cases l with
    | nil =>
      cases a <;> simp [step,rightStep,hd,flip,Option.map_map,Function.comp_def]
    | cons c l =>
      rcases c with ⟨b,t⟩
      cases hh : table.cell q b t with
      | none => simp [step,rightStep,hd,flip,hh]
      | some i => cases hi : i.cross <;> simp [step,rightStep,hd,hh,hi,flip]

variable [Primcodable H] [Primcodable B] [Primcodable T]

 theorem primrec_flip : Primrec (flip (H := H) (B := B) (T := T)) :=
  Sector.primrec_mk Sector.primrec_right Sector.primrec_head Sector.primrec_left
    Sector.primrec_rb Sector.primrec_lb

variable [Fintype H] [Fintype B] [Fintype T] (table : Table H B T)

 theorem primrec_rightStep : Primrec (rightStep table) := by
  have hb : Primrec (fun v : Sector H B T =>
      if v.rightBoundary then (table.boundary v.head).map (fun q => {v with head := q}) else none) := by
    simp only [← Bool.cond_eq_ite]
    apply Primrec.cond Sector.primrec_rb
    · apply Primrec.option_map ((Primrec.dom_finite table.boundary).comp Sector.primrec_head)
      exact (Sector.primrec_mk (Sector.primrec_left.comp Primrec.fst) Primrec.snd
        (Sector.primrec_right.comp Primrec.fst) (Sector.primrec_lb.comp Primrec.fst)
        (Sector.primrec_rb.comp Primrec.fst)).to₂
    · exact Primrec.const none
  have hc : Primrec₂ (fun (v : Sector H B T) (p : (B×T) × List (B×T)) =>
      (table.cell v.head p.1.1 p.1.2).map fun a =>
        if a.cross then {v with left := (p.1.1,a.tag)::v.left,head := a.head,right := p.2}
        else {v with head := a.head,right := (p.1.1,a.tag)::p.2}) := by
    unfold Primrec₂
    apply Primrec.option_map
      ((Primrec.dom_finite (fun p : H × B × T => table.cell p.1 p.2.1 p.2.2)).comp
        ((Sector.primrec_head.comp Primrec.fst).pair
          ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
            (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))
    unfold Primrec₂
    let α := (Sector H B T × ((B×T) × List (B×T))) × Instruction H T
    have hv : Primrec (fun p : α => p.1.1) := Primrec.fst.comp Primrec.fst
    have hp : Primrec (fun p : α => p.1.2) := Primrec.snd.comp Primrec.fst
    have hi : Primrec (fun p : α => p.2) := Primrec.snd
    have hcell : Primrec (fun p : α => (p.1.2.1.1,p.2.tag)) :=
      (Primrec.fst.comp (Primrec.fst.comp hp)).pair (Instruction.primrec_tag.comp hi)
    dsimp only
    simp only [← Bool.cond_eq_ite]
    apply Primrec.cond (Instruction.primrec_cross.comp hi)
    · exact Sector.primrec_mk (Primrec.list_cons.comp hcell (Sector.primrec_left.comp hv))
        (Instruction.primrec_head.comp hi) (Primrec.snd.comp hp)
        (Sector.primrec_lb.comp hv) (Sector.primrec_rb.comp hv)
    · exact Sector.primrec_mk (Sector.primrec_left.comp hv)
        (Instruction.primrec_head.comp hi) (Primrec.list_cons.comp hcell (Primrec.snd.comp hp))
        (Sector.primrec_lb.comp hv) (Sector.primrec_rb.comp hv)
  exact (Primrec.list_casesOn Sector.primrec_right hb hc).of_eq fun v => by
    cases hr : v.right with
    | nil => simp [hr,rightStep]
    | cons c r => cases c; simp [hr,rightStep]

 theorem primrec_step : Primrec (step table) := by
  have hg : Primrec (fun v : Sector H B T => decide (table.direction v.head = .right)) :=
    (Primrec.dom_finite (fun q => decide (table.direction q = .right))).comp Sector.primrec_head
  exact (Primrec.cond hg (primrec_rightStep table)
    (Primrec.option_map ((primrec_rightStep table).comp primrec_flip)
      (primrec_flip.comp Primrec.snd).to₂)).of_eq fun v => by
        simpa only [Bool.cond_decide] using (step_rightStep table v).symm

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

def stepBool (v w : Sector H B T) : Bool := decide (step table v = some w)

 theorem primrec_stepBool : Primrec₂ (stepBool table) :=
  (Primrec.eq.decide.comp ((primrec_step table).comp Primrec.fst)
    (Primrec.option_some.comp Primrec.snd)).to₂

noncomputable def componentList (v : Sector H B T) : List (Sector H B T) :=
  FiniteAlgebraicEnvelopes.Effect.Graph.component (stepBool table) (universeList v) v

omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_componentList (v w : Sector H B T) :
    w ∈ componentList table v ↔ EqvGen (Step table) v w := by
  change w ∈ componentList table v ↔ EqvGen (fun a b => step table a = some b) v w
  simpa only [componentList,stepBool,decide_eq_true_eq,Step] using
    (FiniteAlgebraicEnvelopes.Effect.Graph.mem_component_iff (stepBool table)
      (b := w) ((mem_universeList v v).mpr rfl) (by
        intro c hc d hd
        rw [mem_universeList] at hc ⊢
        rcases hd with hd | hd
        · exact (step_skeleton table ((show Step table c d from of_decide_eq_true (p := step table c = some d) hd))).symm.trans hc
        · exact (step_skeleton table ((show Step table d c from of_decide_eq_true (p := step table d = some c) hd))).trans hc))

 theorem primrec_componentList : Primrec (componentList table) :=
  (primrec_component (primrec_stepBool table)).comp primrec_universeList Primrec.id

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Effect
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {α : Type*} [Primcodable α] [DecidableEq α]

 def priorityList (p q : α → Bool) (s : List α) : List α :=
  if (s.filter p).isEmpty then
    if (s.filter q).isEmpty then s else s.filter q
  else s.filter p

omit [Primcodable α] in
 theorem priorityList_toFinset (p q : α → Bool) (s : List α) :
    (priorityList p q s).toFinset =
      Compiler.prioritySet (fun a => p a = true) (fun a => q a = true) s.toFinset := by
  have hp : (s.filter p).isEmpty = true ↔ ¬ (s.toFinset.filter (fun a => p a = true)).Nonempty := by
    simp
  have hq : (s.filter q).isEmpty = true ↔ ¬ (s.toFinset.filter (fun a => q a = true)).Nonempty := by
    simp
  simp only [priorityList,Compiler.prioritySet,hp,hq]
  split_ifs <;> simp_all

 theorem primrec_listIsEmpty : Primrec (List.isEmpty (α := α)) :=
  (Primrec.eq.decide.comp Primrec.id (Primrec.const [])).of_eq fun l => by
    cases l <;> simp

 theorem primrec_priorityList {p q : α → Bool} (hp : Primrec p) (hq : Primrec q) :
    Primrec (priorityList p q) := by
  have hf := primrec_listFilter Primrec.id (hp.comp Primrec.snd).to₂
  have hg := primrec_listFilter Primrec.id (hq.comp Primrec.snd).to₂
  unfold priorityList
  simp only [← Bool.cond_eq_ite]
  exact Primrec.cond (primrec_listIsEmpty.comp hf)
    (Primrec.cond (primrec_listIsEmpty.comp hg) Primrec.id hg) hf

variable [LinearOrder α]

omit [DecidableEq α] in
 theorem primrec_listMin (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec (List.min? (α := α)) := by
  have hmin : Primrec₂ (min : α → α → α) := by
    exact (Primrec.ite hle Primrec.fst Primrec.snd).of_eq fun p => by
      simp only [min_def]
  have hfold : Primrec₂ (fun (_ : List α) (p : α × List α) => some (p.2.foldl min p.1)) := by
    exact (Primrec.option_some.comp (Primrec.list_foldl (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd) (hmin.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)).to₂
  exact (Primrec.list_casesOn Primrec.id (Primrec.const none) hfold).of_eq fun l =>
    by cases l <;> rfl

omit [Primcodable α] in
 theorem minList_eq (s : List α) (t : Finset α) (h : t.Nonempty)
    (he : s.toFinset = t) (a : α) : s.min?.getD a = t.min' h := by
  have hm : s.min? = some (t.min' h) := by
    rw [List.min?_eq_some_iff]
    constructor
    · rw [← List.mem_toFinset,he]; exact Finset.min'_mem _ _
    · intro b hb
      exact Finset.min'_le _ _ (he ▸ List.mem_toFinset.mpr hb)
  rw [hm]; rfl

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect
variable {H B T : Type*} [Primcodable H] [Primcodable B] [Primcodable T]
  [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T]
  [LinearOrder (Sector H B T)]
  (table : Table H B T) (P Q : Sector H B T → Prop) [DecidablePred P] [DecidablePred Q]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
 theorem representative_list (v : Sector H B T) :
    representative table P Q v =
      (priorityList (fun x => decide (P x)) (fun x => decide (Q x)) (componentList table v)).min?.getD v := by
  symm
  apply minList_eq
  rw [priorityList_toFinset]
  have he : (componentList table v).toFinset = literalComponent table v := by
    ext w
    simp only [List.mem_toFinset,mem_componentList,mem_literalComponent]
  simp only [decide_eq_true_eq,he]

 theorem primrec_representative
    (hle : PrimrecRel (fun a b : Sector H B T => a ≤ b))
    (hp : PrimrecPred P) (hq : PrimrecPred Q) : Primrec (representative table P Q) := by
  exact (Primrec.option_getD.comp
    ((primrec_listMin hle).comp ((primrec_priorityList hp.decide hq.decide).comp
      (primrec_componentList table))) Primrec.id).of_eq fun v => (representative_list table P Q v).symm

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Effect
@[instance_reducible] noncomputable def finitePrimcodable (α : Type*) [Fintype α] : Primcodable α :=
  Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)

@[instance_reducible] def codeOrder (α : Type*) [Primcodable α] : LinearOrder α :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

theorem primrec_codeOrder (α : Type*) [Primcodable α] :
    letI := codeOrder α
    PrimrecRel (fun a b : α => a ≤ b) :=
  Primrec.nat_le.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)
end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect
noncomputable instance {S : Type*} [Fintype S] : Primcodable (Base S) := finitePrimcodable _
noncomputable instance {S Γ : Type*} [Fintype S] [Fintype Γ] : Primcodable (Tag S Γ) := finitePrimcodable _
noncomputable instance {S Q : Type*} [Fintype S] [Fintype Q] : Primcodable (Control.Head S Q) := finitePrimcodable _
noncomputable instance {H : Type*} [Fintype H] : Primcodable (Surface.Head H) := finitePrimcodable _

namespace Control
variable {S Γ Q : Type*} [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
 theorem primrec_entry (blank : Γ) : PrimrecPred (Entry (S := S) (Q := Q) blank) := by
  exact (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.initial)).and
    (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right)
      (Primrec.const (some (Validator.cell blank .cutD))))

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
 theorem primrec_success : PrimrecPred (Success (S := S) (Γ := Γ) (Q := Q)) := by
  exact (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const (Head.machine .ok))).and
    ((Primrec.eq.comp Scan.Sector.primrec_right (Primrec.const [])).and
      (Primrec.eq.comp Scan.Sector.primrec_rb (Primrec.const true)))

 theorem primrec_representative (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
    [LinearOrder (Sector S Γ Q)]
    (hle : PrimrecRel (fun a b : Sector S Γ Q => a ≤ b)) : Primrec (representative A M) :=
  Scan.primrec_representative _ _ _ hle (primrec_entry A.blank) primrec_success
end Control

namespace Surface
open Scan
variable {S Γ H : Type*} [Fintype S] [Fintype Γ] [Fintype H]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq H] (blank : Γ)

 def cleanAnchor (c : Base S × Tag S Γ) : Bool :=
  match c.1 with
  | .anchor _ => decide (c.2 = clean blank)
  | _ => false

omit [Fintype S] [Fintype Γ] [Fintype H] [DecidableEq H] in
 theorem rawSweep_takeDrop (l r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H) blank l r lb rb =
      ⟨l.dropWhile (cleanAnchor blank),.raw,
        (l.takeWhile (cleanAnchor blank)).reverse ++ r,lb,rb⟩ := by
  induction l generalizing r with
  | nil => rfl
  | cons c l ih =>
    rcases c with ⟨b,t⟩
    cases b with
    | anchor a =>
      by_cases h : t = clean blank
      · simp [rawSweep,h,cleanAnchor,ih,List.reverse_cons,List.append_assoc]
      · simp [rawSweep,h,cleanAnchor]
    | cutC | cutD | workspace => simp [rawSweep,cleanAnchor]

omit [DecidableEq H] in
 theorem primrec_rawSweep : Primrec (fun p : (Cells S Γ × Cells S Γ) × Bool × Bool =>
    rawSweep (H := H) blank p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hp := Primrec.dom_finite (cleanAnchor (S := S) blank)
  exact (Scan.Sector.primrec_mk
    ((Primrec.list_dropWhile hp).comp (Primrec.fst.comp Primrec.fst))
    (Primrec.const Head.raw)
    (Primrec.list_append.comp
      (Primrec.list_reverse.comp ((Primrec.list_takeWhile hp).comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).of_eq
      fun p => (rawSweep_takeDrop blank _ _ _ _).symm

 theorem primrec_rawNormal : Primrec (rawNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H => v.head = .raw) :=
    Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.raw)
  have hh : Primrec (fun v : Sector S Γ H => if v.head = .raw then
      rawSweep blank v.left v.right v.leftBoundary v.rightBoundary else v) :=
    Primrec.ite hg ((primrec_rawSweep blank).comp
      ((Scan.Sector.primrec_left.pair Scan.Sector.primrec_right).pair
        (Scan.Sector.primrec_lb.pair Scan.Sector.primrec_rb))) Primrec.id
  exact hh.of_eq fun v => by cases h : v.head <;> simp [rawNormal,h]

omit [Fintype S] [Fintype Γ] in
 theorem trimQuota_drop (l : Cells S Γ) :
    trimQuota blank l = l.dropWhile (fun c => decide (c = Validator.cell blank .workspace)) := by
  induction l with
  | nil => rfl
  | cons c l ih => by_cases h : c = Validator.cell blank .workspace <;>
      simp [trimQuota,h,ih]

 theorem primrec_trimQuota : Primrec (trimQuota (S := S) blank) :=
  (Primrec.list_dropWhile (Primrec.dom_finite _)).of_eq fun l => (trimQuota_drop blank l).symm

 theorem primrec_quotaNormal : Primrec (quotaNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H =>
      v.head = .pending ∧ v.right.head? = some (Validator.cell blank .cutD)) :=
    (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.pending)).and
      (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right) (Primrec.const _))
  have hh : Primrec (fun v : Sector S Γ H =>
      if v.head = .pending ∧ v.right.head? = some (Validator.cell blank .cutD)
      then {v with left := trimQuota blank v.left} else v) :=
    Primrec.ite hg
      (Scan.Sector.primrec_mk ((primrec_trimQuota blank).comp Scan.Sector.primrec_left)
        Scan.Sector.primrec_head Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
      Primrec.id
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases q <;> cases r <;> simp [quotaNormal]

 theorem primrec_unmerge : Primrec (unmerge (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H =>
      v.head = .pending ∧ v.left.head? = some (Validator.cell blank .cutC) ∧
        v.right.head? = some (Validator.cell blank .cutD)) :=
    (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.pending)).and
      ((Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_left) (Primrec.const _)).and
        (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right) (Primrec.const _)))
  have hl : Primrec (fun v : Sector S Γ H => rawNormal (H := H) blank
      ⟨v.left.tail,.raw,[],v.leftBoundary,true⟩) :=
    (primrec_rawNormal (H := H) blank).comp (Scan.Sector.primrec_mk
      (Primrec.list_tail.comp Scan.Sector.primrec_left) (Primrec.const Head.raw)
      (Primrec.const []) Scan.Sector.primrec_lb (Primrec.const true))
  have hr : Primrec (fun v : Sector S Γ H => rawNormal (H := H) blank
      ⟨[],.raw,v.right.tail,true,v.rightBoundary⟩) :=
    (primrec_rawNormal (H := H) blank).comp (Scan.Sector.primrec_mk (Primrec.const [])
      (Primrec.const Head.raw) (Primrec.list_tail.comp Scan.Sector.primrec_right)
      (Primrec.const true) Scan.Sector.primrec_rb)
  have hh : Primrec (fun v : Sector S Γ H =>
      if v.head = .pending ∧ v.left.head? = some (Validator.cell blank .cutC) ∧
        v.right.head? = some (Validator.cell blank .cutD)
      then [rawNormal blank ⟨v.left.tail,.raw,[],v.leftBoundary,true⟩,
        rawNormal blank ⟨[],.raw,v.right.tail,true,v.rightBoundary⟩]
      else [v]) :=
    Primrec.ite hg (Primrec.list_cons.comp hl
      (Primrec.list_cons.comp hr (Primrec.const [])))
      (Primrec.list_cons.comp Primrec.id (Primrec.const []))
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases l with
    | nil => cases q <;> simp [unmerge]
    | cons c l =>
      cases r with
      | nil => cases q <;> simp [unmerge]
      | cons d r => cases q <;> simp [unmerge]

 theorem primrec_pendingPreprocess : Primrec (pendingPreprocess (S := S) (H := H) blank) :=
  (primrec_unmerge blank).comp (primrec_quotaNormal blank)
omit [DecidableEq S] [DecidableEq Γ] in
 theorem primrec_cleanupOutput : Primrec (Cleanup.output (S := S) blank) := by
  have hfinite : Primrec (fun c : Base S × Tag S Γ =>
      (Cleanup.emit c).map (Cleanup.letter blank)) := Primrec.dom_finite _
  exact (Primrec.listFilterMap Primrec.id (hfinite.comp Primrec.snd).to₂).of_eq fun l => by
    simp only [Cleanup.output, List.map_filterMap, id_eq]

omit [DecidableEq S] [DecidableEq Γ] in
 theorem primrec_cleanupNormal : Primrec (cleanupNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H => v.head = .cleanup) :=
    Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.cleanup)
  have hh : Primrec (fun v : Sector S Γ H => if v.head = .cleanup then
      (⟨[],if v.leftBoundary then .raw else .cleanup,
        Cleanup.output blank v.left.reverse ++ v.right,v.leftBoundary,v.rightBoundary⟩ : Sector S Γ H)
      else v) :=
    Primrec.ite hg (Scan.Sector.primrec_mk (Primrec.const [])
      ((Primrec.dom_finite (fun b : Bool => if b then (Head.raw : Head H) else .cleanup)).comp
        Scan.Sector.primrec_lb)
      (Primrec.list_append.comp ((primrec_cleanupOutput blank).comp
        (Primrec.list_reverse.comp Scan.Sector.primrec_left)) Scan.Sector.primrec_right)
      Scan.Sector.primrec_lb Scan.Sector.primrec_rb) Primrec.id
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases q <;> cases lb <;> rfl

 theorem primrec_cleanupPreprocess : Primrec (cleanupPreprocess (S := S) (H := H) blank) :=
  (primrec_rawNormal blank).comp (primrec_cleanupNormal blank)
end Surface

namespace Scan
variable {H H' B T : Type*} [Primcodable H] [Primcodable H'] [Primcodable B] [Primcodable T]
 theorem primrec_mapHead {f : H → H'} (hf : Primrec f) : Primrec (mapHead (B := B) (T := T) f) :=
  Sector.primrec_mk Sector.primrec_left (hf.comp Sector.primrec_head) Sector.primrec_right
    Sector.primrec_lb Sector.primrec_rb
end Scan

namespace Surface
variable {S Γ Q : Type*} [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [LinearOrder (Control.Sector S Γ Q)]
  (hle : PrimrecRel (fun a b : Control.Sector S Γ Q => a ≤ b))

 include hle in
 theorem primrec_internalPreprocess : Primrec (internalPreprocess A M) := by
  have hp := primrec_pendingPreprocess (S := S) (H := Control.Head S Q) A.blank
  have hc := primrec_cleanupPreprocess (S := S) (H := Control.Head S Q) A.blank
  have hrep := Control.primrec_representative A M hle
  have hl : Primrec (fun w : Control.Sector S Γ Q =>
      pendingPreprocess A.blank (⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩ : Sector S Γ (Control.Head S Q))) :=
    hp.comp (Scan.Sector.primrec_mk Scan.Sector.primrec_left (Primrec.const Head.pending)
      Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
  have hr : Primrec (fun w : Control.Sector S Γ Q =>
      cleanupPreprocess A.blank (⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩ : Sector S Γ (Control.Head S Q))) :=
    hc.comp (Scan.Sector.primrec_mk Scan.Sector.primrec_left (Primrec.const Head.cleanup)
      Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
  exact (Primrec.ite (Control.primrec_entry A.blank) hl
    (Primrec.ite Control.primrec_success (Primrec.list_cons.comp hr (Primrec.const []))
      (Primrec.list_cons.comp (Scan.primrec_mapHead (Primrec.dom_finite Head.internal))
        (Primrec.const [])))).comp hrep

 include hle in
 theorem primrec_preprocess : Primrec (preprocess A M) := by
  let inside : Head (Control.Head S Q) → Control.Head S Q
    | .internal q => q
    | _ => .initial
  have hi : Primrec (fun v : Sector S Γ (Control.Head S Q) =>
      internalPreprocess A M
        ⟨v.left,inside v.head,v.right,v.leftBoundary,v.rightBoundary⟩) :=
    (primrec_internalPreprocess A M hle).comp
      (Scan.Sector.primrec_mk Scan.Sector.primrec_left
        ((Primrec.dom_finite inside).comp Scan.Sector.primrec_head)
        Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
  have hg (q : Head (Control.Head S Q)) :
      PrimrecPred (fun v : Sector S Γ (Control.Head S Q) => v.head = q) :=
    Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const q)
  have hh : Primrec (fun v : Sector S Γ (Control.Head S Q) =>
      if v.head = .raw then [rawNormal A.blank v]
      else if v.head = .pending then pendingPreprocess A.blank v
      else if v.head = .cleanup then [cleanupPreprocess A.blank v]
      else internalPreprocess A M ⟨v.left,inside v.head,v.right,v.leftBoundary,v.rightBoundary⟩) :=
    Primrec.ite (hg .raw)
      (Primrec.list_cons.comp (primrec_rawNormal A.blank) (Primrec.const []))
      (Primrec.ite (hg .pending) (primrec_pendingPreprocess A.blank)
        (Primrec.ite (hg .cleanup)
          (Primrec.list_cons.comp (primrec_cleanupPreprocess A.blank) (Primrec.const [])) hi))
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases q <;> simp [preprocess,inside]

end Surface
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Path
open FiniteAlgebraicEnvelopes.Effect
variable {C H : Type*}

def Sector.code : Sector C H ≃ List C × (H × (List C × (Bool × Bool))) where
  toFun v := (v.left,v.head,v.right,v.leftBoundary,v.rightBoundary)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Primcodable C] [Primcodable H] : Primcodable (Sector C H) :=
  Primcodable.ofEquiv _ Sector.code

variable [Primcodable C] [Primcodable H]

theorem Sector.primrec_code : Primrec (Sector.code (C := C) (H := H)) := Primrec.of_equiv
theorem Sector.primrec_decode : Primrec (Sector.code (C := C) (H := H)).symm :=
  Primrec.of_equiv_symm

theorem Sector.primrec_left : Primrec (Sector.left (C := C) (H := H)) :=
  Primrec.fst.comp Sector.primrec_code
theorem Sector.primrec_head : Primrec (Sector.head (C := C) (H := H)) :=
  Primrec.fst.comp (Primrec.snd.comp Sector.primrec_code)
theorem Sector.primrec_right : Primrec (Sector.right (C := C) (H := H)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code))
theorem Sector.primrec_lb : Primrec (Sector.leftBoundary (C := C) (H := H)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))
theorem Sector.primrec_rb : Primrec (Sector.rightBoundary (C := C) (H := H)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))

theorem Sector.primrec_mk {α : Type*} [Primcodable α]
    {l r : α → List C} {q : α → H} {a b : α → Bool}
    (hl : Primrec l) (hq : Primrec q) (hr : Primrec r) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => (⟨l x,q x,r x,a x,b x⟩ : Sector C H)) :=
  Sector.primrec_decode.comp (hl.pair (hq.pair (hr.pair (ha.pair hb))))

variable [Fintype C] [Fintype H] [DecidableEq C] [DecidableEq H]
noncomputable instance : Primcodable (Letter C H) := finitePrimcodable _
noncomputable instance : Primcodable Shape := finitePrimcodable _

omit [Primcodable C] [Primcodable H] [DecidableEq C] [DecidableEq H] in
 theorem primrec_shape : Primrec (shape (C := C) (H := H)) := by
  have hp : Primrec (fun p : Letter C H × Shape => typeOf p.1 * p.2) := Primrec.dom_finite _
  exact (Primrec.list_foldr Primrec.id (Primrec.const Shape.unit)
    (hp.comp Primrec.snd).to₂).of_eq fun w => by
      induction w with
      | nil => rfl
      | cons a w ih => simpa only [id_eq,List.foldr_cons,shape_cons] using congrArg (typeOf a * ·) ih

omit [Primcodable C] [DecidableEq C] [DecidableEq H] in
 theorem primrec_heads : Primrec (heads (C := C) (H := H)) := by
  have hp : Primrec (fun a : Letter C H => match a with | .head q => some q | _ => none) := Primrec.dom_finite _
  exact Primrec.listFilterMap Primrec.id (hp.comp Primrec.snd).to₂
omit [Primcodable H] [DecidableEq C] [DecidableEq H] in
 theorem primrec_lefts : Primrec (lefts (C := C) (H := H)) := by
  have hp : Primrec (fun a : Letter C H => match a with | .left c => some c | _ => none) := Primrec.dom_finite _
  exact Primrec.listFilterMap Primrec.id (hp.comp Primrec.snd).to₂
omit [Primcodable H] [DecidableEq C] [DecidableEq H] in
 theorem primrec_rights : Primrec (rights (C := C) (H := H)) := by
  have hp : Primrec (fun a : Letter C H => match a with | .right c => some c | _ => none) := Primrec.dom_finite _
  exact Primrec.listFilterMap Primrec.id (hp.comp Primrec.snd).to₂

omit [DecidableEq C] [DecidableEq H] in
 theorem primrec_encode : Primrec (encode (C := C) (H := H)) := by
  have hl : Primrec (fun v : Sector C H => v.left.reverse.map (Letter.left : C → Letter C H)) :=
    Primrec.list_map (Primrec.list_reverse.comp Sector.primrec_left)
      ((Primrec.dom_finite _).comp Primrec.snd).to₂
  have hr : Primrec (fun v : Sector C H => v.right.map (Letter.right : C → Letter C H)) :=
    Primrec.list_map Sector.primrec_right ((Primrec.dom_finite _).comp Primrec.snd).to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp
      ((Primrec.dom_finite (fun b : Bool => if b then ([.enter] : List (Letter C H)) else [])).comp
        Sector.primrec_lb) hl)
      (Primrec.list_cons.comp ((Primrec.dom_finite Letter.head).comp Sector.primrec_head) (Primrec.const []))) hr)
    ((Primrec.dom_finite (fun b : Bool => if b then ([.leave] : List (Letter C H)) else [])).comp
      Sector.primrec_rb)

omit [Primcodable C] [Primcodable H] [DecidableEq C] [DecidableEq H] in
 theorem primrec_glue : Primrec₂ (glue (C := C) (H := H)) := by
  have hn : Primrec (fun p : List (Letter C H) × List (List (Letter C H)) =>
      if p.1 = [] then [] else [p.1]) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const [])) (Primrec.const [])
      (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
  have hc : Primrec₂ (fun (p : List (Letter C H) × List (List (Letter C H)))
      (ct : List (Letter C H) × List (List (Letter C H))) => (p.1++ct.1)::ct.2) :=
    (Primrec.list_cons.comp (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_casesOn Primrec.snd hn hc).to₂.of_eq fun u w => by
    cases w <;> cases u <;> rfl

omit [Primcodable C] [Primcodable H] [Fintype C] [Fintype H] in
 theorem cuts_fold (w : List (Letter C H)) :
    cuts w = w.foldr (fun a cs => if a = .leave then [.leave]::cs else glue [a] cs) [] := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [cuts,ih]

omit [Primcodable C] [Primcodable H] in
 theorem primrec_cuts : Primrec (cuts (C := C) (H := H)) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const Letter.leave))
      (Primrec.list_cons.comp (Primrec.const [Letter.leave]) (Primrec.snd.comp Primrec.snd))
      (primrec_glue.comp (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
        (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun w => (cuts_fold w).symm

omit [Primcodable C] [Primcodable H] [DecidableEq C] [DecidableEq H] in
 theorem primrec_mem (a : Letter C H) : PrimrecPred (fun w : List (Letter C H) => a ∈ w) := by
  exact ((Primrec.eq.comp Primrec.id (Primrec.const a)).exists_mem_list).of_eq fun w => by simp

 theorem primrec_decode : Primrec (decode (C := C) (H := H)) := by
  let make : List (Letter C H) × H → Sector C H := fun p =>
    ⟨(lefts p.1).reverse,p.2,rights p.1,decide (.enter ∈ p.1),decide (.leave ∈ p.1)⟩
  have hm : Primrec make := Sector.primrec_mk
    (Primrec.list_reverse.comp (primrec_lefts.comp Primrec.fst)) Primrec.snd
    (primrec_rights.comp Primrec.fst) ((primrec_mem .enter).decide.comp Primrec.fst)
    ((primrec_mem .leave).decide.comp Primrec.fst)
  have ht : Primrec (fun p : List (Letter C H) × H =>
      if encode (make p) = p.1 then some (make p) else none) :=
    Primrec.ite (Primrec.eq.comp (primrec_encode.comp hm) Primrec.fst)
      (Primrec.option_some.comp hm) (Primrec.const none)
  have hh : Primrec (fun w : List (Letter C H) => if (heads w).length = 1 then
      (heads w).head?.bind (fun q => if encode (make (w,q)) = w then some (make (w,q)) else none)
      else none) :=
    Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp primrec_heads) (Primrec.const 1))
      (Primrec.option_bind (Primrec.list_head?.comp primrec_heads) ht.to₂) (Primrec.const none)
  exact hh.of_eq fun w => by
    unfold decode
    cases h : heads w with
    | nil => simp
    | cons q t => cases t with
      | nil => simp only [List.length_singleton,↓reduceIte,List.head?_cons,Option.bind_some]; rfl
      | cons q' t => simp

 theorem primrec_prepareChunk {P : Sector C H → List (Sector C H)} (hP : Primrec P) :
    Primrec (prepareChunk P) := by
  exact (Primrec.option_casesOn primrec_decode (Primrec.list_cons.comp Primrec.id (Primrec.const []))
    (Primrec.list_map (hP.comp Primrec.snd) (primrec_encode.comp Primrec.snd).to₂).to₂).of_eq
      fun w => by cases h : decode w <;> simp [prepareChunk,h]

 theorem primrec_prepareChunks {P : Sector C H → List (Sector C H)} (hP : Primrec P) :
    Primrec (prepareChunks P) :=
  Primrec.list_flatMap Primrec.id ((primrec_prepareChunk hP).comp Primrec.snd).to₂

 theorem primrec_prepare {P : Sector C H → List (Sector C H)} (hP : Primrec P) :
    Primrec (prepare P) :=
  (primrec_prepareChunks hP).comp primrec_cuts

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H K B T : Type*} [Primcodable H] [Primcodable K] [Primcodable B] [Primcodable T]
 theorem primrec_literal {m : H → K} (hm : Primrec m) : Primrec (literal (B := B) (T := T) m) :=
  Path.Sector.primrec_mk Sector.primrec_left (hm.comp Sector.primrec_head) Sector.primrec_right
    Sector.primrec_lb Sector.primrec_rb
 theorem primrec_unliteral : Primrec (unliteral (H := H) (B := B) (T := T)) :=
  Sector.primrec_mk Path.Sector.primrec_left Path.Sector.primrec_head Path.Sector.primrec_right
    Path.Sector.primrec_lb Path.Sector.primrec_rb
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word
variable {S Γ Q : Type*} [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable S]
  (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [LinearOrder (Control.Sector S Γ Q)]
  (hle : PrimrecRel (fun a b : Control.Sector S Γ Q => a ≤ b))

omit [Primcodable S] in
include hle in
 theorem primrec_sectorPreprocess : Primrec (sectorPreprocess A M) :=
  Primrec.list_map ((Surface.primrec_preprocess A M hle).comp Scan.primrec_unliteral)
    ((Scan.primrec_literal Primrec.id).comp Primrec.snd).to₂

omit [Primcodable S] in
include hle in
 theorem primrec_preprocess : Primrec (preprocess A M) :=
  Path.primrec_prepare (primrec_sectorPreprocess A M hle)

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
    [LinearOrder (Control.Sector S Γ Q)] in
 theorem primrec_raw (blank : Γ) : Primrec (raw (S := S) (Q := Q) blank) := by
  have hp : Primrec (fun w : List S => (⟨[],Surface.Head.raw,
      w.map (Validator.cell blank ∘ Base.anchor),true,true⟩ : Surface.Sector S Γ (Control.Head S Q))) :=
    Scan.Sector.primrec_mk (Primrec.const []) (Primrec.const Surface.Head.raw)
      (Primrec.list_map Primrec.id ((Primrec.dom_finite _).comp Primrec.snd).to₂)
      (Primrec.const true) (Primrec.const true)
  exact Path.primrec_encode.comp ((Scan.primrec_literal Primrec.id).comp hp)

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
    [LinearOrder (Control.Sector S Γ Q)] in
 theorem primrec_rawLetters : Primrec (rawLetters (S := S) (Γ := Γ) (Q := Q)) := by
  have hp : Primrec (fun a : Letter S Γ Q => match a with
      | .right (.anchor s,_) => some s | _ => none) := Primrec.dom_finite _
  exact Primrec.listFilterMap Primrec.id (hp.comp Primrec.snd).to₂

omit [LinearOrder (Control.Sector S Γ Q)] in
 theorem primrec_readRaw (blank : Γ) : Primrec (readRaw (S := S) (Q := Q) blank) :=
  Primrec.ite (Primrec.eq.comp ((primrec_raw blank).comp primrec_rawLetters) Primrec.id)
    (Primrec.option_some.comp primrec_rawLetters) (Primrec.const none)

omit [LinearOrder (Control.Sector S Γ Q)] in
 theorem primrec_classify (blank : Γ) : Primrec (classify (S := S) (Q := Q) blank) := by
  exact (Primrec.option_casesOn (primrec_readRaw blank) Primrec.sumInl
    (Primrec.sumInr.comp Primrec.snd).to₂).of_eq fun w => by
      cases h : readRaw blank w <;> simp [classify,h]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
    [LinearOrder (Control.Sector S Γ Q)] in
 theorem primrec_realize (blank : Γ) : Primrec (realize (S := S) (Q := Q) blank) := by
  exact (Primrec.sumCasesOn Primrec.id Primrec.snd.to₂
    ((primrec_raw blank).comp Primrec.snd).to₂).of_eq fun w => by cases w <;> rfl

include hle in
 theorem partrec_partialNormal {f : List S →. List S} (hf : Partrec f) :
    Partrec (partialNormal A M f) := by
  have hp : Primrec (fun w : List (Letter S Γ Q) =>
      (preprocess A M w).map (classify A.blank)) :=
    Primrec.list_map (primrec_preprocess A M hle) ((primrec_classify A.blank).comp Primrec.snd).to₂
  have hr : Primrec (fun w : List (Item S Γ Q) => w.flatMap (realize A.blank)) :=
    Primrec.list_flatMap Primrec.id ((primrec_realize A.blank).comp Primrec.snd).to₂
  have hb : Partrec (fun w : List (Letter S Γ Q) =>
      (RawRuns.partialSource f ((preprocess A M w).map (classify A.blank))).map
        (List.flatMap (realize A.blank))) :=
    ((RawRuns.partrec_partialSource hf).comp hp.to_comp).map (hr.to_comp.comp Computable.snd).to₂
  have ho : Primrec (fun w : List (Letter S Γ Q) =>
      if Path.shape w = .zero then none else some w) :=
    Primrec.ite (Primrec.eq.comp Path.primrec_shape (Primrec.const Path.Shape.zero))
      (Primrec.const none) Primrec.option_some
  exact (Partrec.optionCasesOn_right ho.to_comp (Computable.const [Path.Letter.zero])
    (hb.comp Computable.snd).to₂).of_eq fun w => by
      by_cases h : Path.shape w = .zero <;> simp [h,partialNormal]

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ)

theorem semanticStep_lift_head (q : Q) (l : List (Tag S Γ)) (t : Tag S Γ) (r : List (Tag S Γ))
    {d : SemanticTape Γ Q} (h : SemanticStep M (interpret A (⟨q,l,t::r⟩ : Tape)) d) :
    ∃ e, TapeStep M (⟨q,l,t::r⟩ : Tape) e ∧ interpret A e = d := by
  unfold SemanticStep semanticStep interpret at h
  simp only [List.map_cons,Stream'.appendStream',Stream'.head_cons] at h
  cases hc : M.transition q t.work with
  | none => simp only [hc,Option.map_none] at h; cases h
  | some cmd =>
    simp only [hc,Option.map_some,Option.some.injEq] at h
    subst d
    rcases cmd with ⟨q',a,mv⟩
    cases mv with
    | stay => exact ⟨_,.stay hc rfl,rfl⟩
    | right => exact ⟨_,.right hc rfl,rfl⟩
    | left =>
      cases l with
      | nil => exact ⟨_,.leftEdge hc rfl,rfl⟩
      | cons b l => exact ⟨_,.left hc rfl,rfl⟩

/-- Infinite semantic transitions can always be realized by materializing at
most one implicit blank. This is a completeness statement, not an assumption
on accepting trajectories. -/
theorem semanticStep_lift {c : Tape (S := S) (Γ := Γ) (Q := Q)}
    {d : SemanticTape Γ Q} (h : SemanticStep M (interpret A c) d) :
    ∃ e, UnboundedStep A M c e ∧ interpret A e = d := by
  rcases c with ⟨q,l,r⟩
  cases r with
  | nil =>
    have hh : SemanticStep M (interpret A (⟨q,l,[clean A.blank]⟩ : Tape)) d := by
      have hp := interpret_pad A (⟨q,l,[]⟩ : Tape) 1
      simpa only [pad,List.nil_append,List.replicate_one] using hp ▸ h
    obtain ⟨e,he,hde⟩ := semanticStep_lift_head A M q l (clean A.blank) [] hh
    exact ⟨e,.extend he,hde⟩
  | cons t r =>
    obtain ⟨e,he,hde⟩ := semanticStep_lift_head A M q l t r h
    exact ⟨e,.within he,hde⟩

 theorem semanticRun_lift {c : Tape (S := S) (Γ := Γ) (Q := Q)}
    {d : SemanticTape Γ Q} (h : ReflTransGen (SemanticStep M) (interpret A c) d) :
    ∃ e, ReflTransGen (UnboundedStep A M) c e ∧ interpret A e = d := by
  induction h with
  | refl => exact ⟨c,.refl,rfl⟩
  | tail _ hs ih =>
    rcases ih with ⟨e,he,rfl⟩
    rcases semanticStep_lift A M hs with ⟨f,hf,rfl⟩
    exact ⟨f,he.tail hf,rfl⟩

 theorem semantic_halted_iff (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    semanticStep M (interpret A c) = none ↔ Halted A M c := by
  rcases c with ⟨q,l,r⟩
  cases r <;> simp [Halted,interpret,semanticStep,Stream'.appendStream',clean,
    Stream'.head,Stream'.get,Stream'.const,Stream'.cons]

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI

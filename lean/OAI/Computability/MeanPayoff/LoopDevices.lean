import OAI.Computability.MeanPayoff.VectorDevices

namespace OAI

section
namespace MeanPayoff.TreeDevice.Forest
open RegisterBits BinaryData
open BinaryData.Take (advance_add)

def encode (xs : List Data) : List Bool := xs.flatMap BinaryData.encode
@[simp] theorem encode_nil : encode [] = [] := rfl
@[simp] theorem encode_cons (x : Data) (xs : List Data) :
    encode (x::xs) = BinaryData.encode x++encode xs := rfl
@[simp] theorem encode_append (a b : List Data) : encode (a++b) = encode a++encode b := List.flatMap_append

structure Layout where
  a : List Data
  b : List Data
  c : List Data

def stack (x : Layout) (suffix : List Bool) := core (encode x.a++suffix) (encode x.b) (encode x.c)

structure Segment {α : Type} (s t : α → Layout) where
  program : RegisterBits.Program 5
  limit : α → ℕ
  correct : ∀ x suffix out bits,
    advance program bits ⟨some program.start,stack (s x) suffix,out⟩ (limit x) =
      ⟨none,stack (t x) suffix,out⟩

noncomputable abbrev seqFlow {α : Type} {s t u : α → Layout} (P : Segment s t) (Q : Segment t u) :
    Flow.Program 5 where
  nodes := 2
  start := 0
  block := ![P.program,Q.program]
  read _ := 0
  next p _ _ := if p=0 then some ⟨1,.keep,none⟩ else none

noncomputable def Segment.seq {α : Type} {s t u : α → Layout} (P : Segment s t) (Q : Segment t u) :
    Segment s u where
  program := Flow.compile (seqFlow P Q)
  limit x := P.limit x+Q.limit x+2
  correct x suffix out bits := by
    obtain ⟨m,hm,he⟩ := Flow.hop (seqFlow P Q) 0 1 _ _ out bits _
      (P.correct x suffix out bits) (by intros; rfl)
    obtain ⟨n,hn,he'⟩ := Flow.finish (seqFlow P Q) 1 _ _ out (fun j => bits (m+j)) _
      (Q.correct x suffix out _) (by intros; rfl)
    apply advance_pad _ _ _ bits (n := m+n) (by omega) ?_ rfl
    change advance _ bits (Flow.state (seqFlow P Q) 0 _ out) _ = _
    rw [advance_add,he,he']

def Segment.cast {α : Type} {s t s' t' : α → Layout} (P : Segment s t)
    (hs : s'=s) (ht : t'=t) : Segment s' t' := hs ▸ ht ▸ P

noncomputable def move01 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨x z::a z,b z,c z⟩) (fun z => ⟨a z,x z::b z,c z⟩) where
  program := moveCode 0 1
  limit z := 6*treeSize (x z)+3
  correct z suffix out bits := by
    simpa only [stack,encode_cons,List.append_assoc] using
      TreeDevice.move01 (x z) (encode (a z)++suffix) (encode (b z)) (encode (c z)) out bits

noncomputable def move02 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨x z::a z,b z,c z⟩) (fun z => ⟨a z,b z,x z::c z⟩) where
  program := moveCode 0 2
  limit z := 6*treeSize (x z)+3
  correct z suffix out bits := by
    simpa only [stack,encode_cons,List.append_assoc] using
      TreeDevice.move02 (x z) (encode (a z)++suffix) (encode (b z)) (encode (c z)) out bits

noncomputable def move10 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨a z,x z::b z,c z⟩) (fun z => ⟨x z::a z,b z,c z⟩) where
  program := moveCode 1 0
  limit z := 6*treeSize (x z)+3
  correct z suffix out bits := by
    simpa only [stack,encode_cons,List.append_assoc] using
      TreeDevice.move10 (x z) (encode (b z)) (encode (a z)++suffix) (encode (c z)) out bits

noncomputable def move20 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨a z,b z,x z::c z⟩) (fun z => ⟨x z::a z,b z,c z⟩) where
  program := moveCode 2 0
  limit z := 6*treeSize (x z)+3
  correct z suffix out bits := by
    simpa only [stack,encode_cons,List.append_assoc] using
      TreeDevice.move20 (x z) (encode (c z)) (encode (a z)++suffix) (encode (b z)) out bits

noncomputable def swap {α : Type} (x y : α → Data) (a : α → List Data) :
    Segment (fun z => ⟨x z::y z::a z,[],[]⟩) (fun z => ⟨y z::x z::a z,[],[]⟩) :=
  (move01 x (fun z => y z::a z) (fun _ => []) (fun _ => [])).seq
    ((move02 y a (fun z => [x z]) (fun _ => [])).seq
      ((move10 x a (fun _ => []) (fun z => [y z])).seq
        (move20 y (fun z => x z::a z) (fun _ => []) (fun _ => []))))

def bitOp (i : Fin 5) (op : BinaryStack.Op) : RegisterBits.Program 5 where
  states := 2
  start := 0
  read _ := i
  transition q _ _ := if q=0 then some ⟨1,op,none⟩ else none

theorem bitOp_runs (i : Fin 5) (op : BinaryStack.Op) (s : Fin 5 → List Bool)
    (out : List Bool) (bits : ℕ → Bool) :
    advance (bitOp i op) bits ⟨some (bitOp i op).start,s,out⟩ 2 =
      ⟨none,Function.update s i (BinaryStack.applyOp op (s i)),out⟩ := by
  simp [advance,RegisterBits.step,bitOp]

def unpair {α : Type} (x y : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨Data.pair (x z) (y z)::a z,b z,c z⟩)
      (fun z => ⟨x z::y z::a z,b z,c z⟩) where
  program := bitOp 0 .pop
  limit _ := 2
  correct z suffix out bits := by
    rw [bitOp_runs]
    simp only [stack,encode_cons,BinaryData.encode,List.cons_append,List.append_assoc,core_zero,
      BinaryStack.applyOp,List.tail_cons]
    congr 1
    funext i; fin_cases i <;> rfl

def pair {α : Type} (x y : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨x z::y z::a z,b z,c z⟩)
      (fun z => ⟨Data.pair (x z) (y z)::a z,b z,c z⟩) where
  program := bitOp 0 (.push true)
  limit _ := 2
  correct z suffix out bits := by
    rw [bitOp_runs]
    simp only [stack,encode_cons,BinaryData.encode,List.cons_append,List.append_assoc,core_zero,
      BinaryStack.applyOp]
    congr 1
    funext i; fin_cases i <;> rfl

noncomputable def applyDevice {α β γ : Type} {ea : β → Data} {eb : γ → Data} {f : β → γ}
    (F : Device ea eb f) (x : α → β) (a : α → List Data) :
    Segment (fun z => ⟨ea (x z)::a z,[],[]⟩) (fun z => ⟨eb (f (x z))::a z,[],[]⟩) where
  program := F.program
  limit z := F.limit (x z)
  correct z suffix out bits := by
    simpa only [store,stack,encode_cons,encode_nil,core,List.append_assoc] using
      F.correct (x z) (encode (a z)++suffix) out bits

noncomputable def toDevice {α β : Type} (ea : α → Data) (eb : β → Data) (f : α → β)
    (P : Segment (fun z => ⟨[ea z],[],[]⟩) (fun z => ⟨[eb (f z)],[],[]⟩)) : Device ea eb f :=
  ofProgram ea eb f P.program P.limit (by
    intros x suffix out bits
    simpa only [stack,encode_cons,encode_nil,List.append_nil,core,store] using P.correct x suffix out bits)

end MeanPayoff.TreeDevice.Forest
namespace MeanPayoff.TreeDevice.Forest
open RegisterBits BinaryData

noncomputable def copy01 {α : Type} (x : α → Data) (a b c : α → List Data) :
    Segment (fun z => ⟨x z::a z,b z,c z⟩) (fun z => ⟨x z::a z,x z::b z,c z⟩) where
  program := rename Copy.program (slots (0:Fin 3) 1)
  limit z := 7*treeSize (x z)+3
  correct z suffix out bits := by
    have h := copy_tree (0:Fin 3) 1 (by decide)
      (core (BinaryData.encode (x z)++(encode (a z)++suffix)) (encode (b z)) (encode (c z)))
      out (x z) (encode (a z)++suffix) (encode (b z)) rfl rfl rfl rfl bits
    simp only [stack,encode_cons,List.append_assoc]
    refine h.trans ?_
    apply Take.config_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl

noncomputable def duplicate {α : Type} (x : α → Data) (a : α → List Data) :
    Segment (fun z => ⟨x z::a z,[],[]⟩) (fun z => ⟨x z::x z::a z,[],[]⟩) :=
  (copy01 x a (fun _ => []) (fun _ => [])).seq
    (move10 x (fun z => x z::a z) (fun _ => []) (fun _ => []))

def erase (i : Fin 5) : RegisterBits.Program 5 where
  states := 1
  start := 0
  read _ := i
  transition _ top _ := match top with
    | none => none
    | some _ => some ⟨0,.pop,none⟩

theorem erase_runs (i : Fin 5) (s : Fin 5 → List Bool) (out : List Bool) (bits : ℕ → Bool) :
    advance (erase i) bits ⟨some (erase i).start,s,out⟩ ((s i).length+1) =
      ⟨none,Function.update s i [],out⟩ := by
  generalize hx : s i = xs
  induction xs generalizing s bits with
  | nil => simp [hx,advance,RegisterBits.step,erase]
  | cons b xs ih =>
    rw [show (b::xs).length+1 = 1+(xs.length+1) by simp; omega,Take.advance_add]
    have hs : advance (erase i) bits ⟨some (erase i).start,s,out⟩ 1 =
        ⟨some (erase i).start,Function.update s i xs,out⟩ := by
      simp [advance,RegisterBits.step,erase,hx,BinaryStack.applyOp]
    rw [hs,ih _ _ (by simp)]
    simp

noncomputable def drop {α : Type} (x : α → Data) (a : α → List Data) :
    Segment (fun z => ⟨x z::a z,[],[]⟩) (fun z => ⟨a z,[],[]⟩) :=
  (move01 x a (fun _ => []) (fun _ => [])).seq {
    program := erase 1
    limit z := treeSize (x z)+1
    correct := by
      intro z suffix out bits
      have h := erase_runs (1:Fin 5) (stack ⟨a z,[x z],[]⟩ suffix) out bits
      simp only [stack,encode_cons,encode_nil,List.append_nil] at h ⊢
      refine h.trans ?_
      apply Take.config_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl }

end MeanPayoff.TreeDevice.Forest

namespace MeanPayoff.TreeDevice
open BinaryData Forest

def product {α β : Type} (ea : α → Data) (eb : β → Data) (x : α × β) : Data := .pair (ea x.1) (eb x.2)

noncomputable def pairMap {α β γ δ : Type} {ea : α → Data} {eb : β → Data}
    {ec : γ → Data} {ed : δ → Data} {f : α → β} {g : γ → δ}
    (F : Device ea eb f) (G : Device ec ed g) :
    Device (product ea ec) (product eb ed) (fun z : α × γ => (f z.1,g z.2)) :=
  toDevice _ _ _ <|
    (unpair (fun z : α × γ => ea z.1) (fun z : α × γ => ec z.2) (fun _ => []) (fun _ => []) (fun _ => [])).seq
      ((applyDevice F Prod.fst (fun z : α × γ => [ec z.2])).seq
        ((swap (fun z : α × γ => eb (f z.1)) (fun z : α × γ => ec z.2) (fun _ => [])).seq
          ((applyDevice G Prod.snd (fun z : α × γ => [eb (f z.1)])).seq
            ((swap (fun z : α × γ => ed (g z.2)) (fun z : α × γ => eb (f z.1)) (fun _ => [])).seq
              (pair (fun z : α × γ => eb (f z.1)) (fun z : α × γ => ed (g z.2)) (fun _ => []) (fun _ => []) (fun _ => []))))))

noncomputable def dup {α : Type} (ea : α → Data) : Device ea (product ea ea) (fun x => (x,x)) :=
  toDevice _ _ _ <| (duplicate ea (fun _ => [])).seq
    (pair ea ea (fun _ => []) (fun _ => []) (fun _ => []))

noncomputable def fanout {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : α → γ} (F : Device ea eb f) (G : Device ea ec g) :
    Device ea (product eb ec) (fun x => (f x,g x)) :=
  compose (dup ea) (pairMap F G)

noncomputable def first {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device (product ea eb) ea Prod.fst :=
  toDevice _ _ _ <|
    (unpair (fun z : α × β => ea z.1) (fun z : α × β => eb z.2) (fun _ => []) (fun _ => []) (fun _ => [])).seq
      ((swap (fun z : α × β => ea z.1) (fun z : α × β => eb z.2) (fun _ => [])).seq
        (drop (fun z : α × β => eb z.2) (fun z : α × β => [ea z.1])))

noncomputable def second {α β : Type} (ea : α → Data) (eb : β → Data) :
    Device (product ea eb) eb Prod.snd :=
  toDevice _ _ _ <|
    (unpair (fun z : α × β => ea z.1) (fun z : α × β => eb z.2) (fun _ => []) (fun _ => []) (fun _ => [])).seq
      (drop (fun z : α × β => ea z.1) (fun z : α × β => [eb z.2]))

end MeanPayoff.TreeDevice
namespace MeanPayoff.TreeDevice.Fold
open RegisterBits BinaryData

noncomputable abbrev flow {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) : Flow.Program 5 where
  nodes := 6
  start := 0
  block := ![skip,moveCode 0 1,skip,moveCode 1 0,F.program,moveCode 1 0]
  read _ := 0
  next p top _ := match p.val with
    | 0 => some ⟨1,.pop,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | 2 => some ⟨if top=some true then 3 else 5,.pop,none⟩
    | 3 => some ⟨4,.push true,none⟩
    | 4 => some ⟨1,.keep,none⟩
    | _ => none

noncomputable abbrev program {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) := Flow.compile (flow F)

noncomputable abbrev cfg {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) (q : Fin 6) (a b out : List Bool) : Config (program F) :=
  Flow.state (flow F) q (core a b []) out

def fold {α β : Type} (f : α × β → α) (a : α) (xs : List β) := xs.foldl (fun a x => f (a,x)) a

def time {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) (a : α) : List β → ℕ
  | [] => 12*treeSize (ea a)+10
  | b::bs => 12*treeSize (ea a)+F.limit (a,b)+11+time F (f (a,b)) bs

theorem loop {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) (a : α) (xs : List β) (suffix out : List Bool) :
    Reaches (program F)
      (cfg F 1 (encode (ea a)++encode (listTree eb xs)++suffix) [] out)
      ⟨none,core (encode (ea (fold f a xs))++suffix) [] [],out⟩ (time F a xs) := by
  induction xs generalizing a with
  | nil =>
    have h₁ : Reaches (program F) (cfg F 1 (encode (ea a)++encode Data.nil++suffix) [] out)
        (cfg F 2 (encode Data.nil++suffix) (encode (ea a)) out) (6*treeSize (ea a)+4) := by
      intro bits
      simpa only [List.append_nil,List.append_assoc] using Flow.hop (flow F) 1 2 _ _ out bits _
        (move01 (ea a) (encode Data.nil++suffix) [] [] out bits) (by intros; rfl)
    have h₂ : Reaches (program F) (cfg F 2 (encode Data.nil++suffix) (encode (ea a)) out)
        (cfg F 5 suffix (encode (ea a)) out) 2 := by
      intro bits
      apply Flow.hop_update (flow F) 2 5 _ _ _ out bits 1 .pop rfl (by intros; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
      simp only [flow,advance,core_zero,core_update]; rfl
    have h₃ : Reaches (program F) (cfg F 5 suffix (encode (ea a)) out)
        ⟨none,core (encode (ea a)++suffix) [] [],out⟩ (6*treeSize (ea a)+4) := by
      intro bits
      simpa only [List.append_nil] using Flow.finish (flow F) 5 _ _ out bits _
        (move10 (ea a) [] suffix [] out bits) (by intros; rfl)
    exact (h₁.trans (h₂.trans h₃)).mono (by simp [time]; omega)
  | cons b bs ih =>
    let tail := encode (listTree eb bs)++suffix
    have h₁ : Reaches (program F)
        (cfg F 1 (encode (ea a)++encode (listTree eb (b::bs))++suffix) [] out)
        (cfg F 2 (encode (listTree eb (b::bs))++suffix) (encode (ea a)) out)
        (6*treeSize (ea a)+4) := by
      intro bits
      simpa only [List.append_nil,List.append_assoc] using Flow.hop (flow F) 1 2 _ _ out bits _
        (move01 (ea a) (encode (listTree eb (b::bs))++suffix) [] [] out bits) (by intros; rfl)
    have h₂ : Reaches (program F)
        (cfg F 2 (encode (listTree eb (b::bs))++suffix) (encode (ea a)) out)
        (cfg F 3 (encode (eb b)++tail) (encode (ea a)) out) 2 := by
      intro bits
      apply Flow.hop_update (flow F) 2 3 _ _ _ out bits 1 .pop rfl (by intros; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
      simp only [flow,advance,core_zero,core_update]
      simp only [listTree,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.tail_cons,
        List.append_assoc,tail]
    have h₃ : Reaches (program F) (cfg F 3 (encode (eb b)++tail) (encode (ea a)) out)
        (cfg F 4 (encode (product ea eb (a,b))++tail) [] out) (6*treeSize (ea a)+4) := by
      intro bits
      apply Flow.hop_update (flow F) 3 4 (core (encode (eb b)++tail) (encode (ea a)) [])
        (core (encode (ea a)++(encode (eb b)++tail)) [] [])
        (core (encode (product ea eb (a,b))++tail) [] []) out bits (6*treeSize (ea a)+3) (.push true)
        (by convert move10 (ea a) [] (encode (eb b)++tail) [] out bits using 1 <;> simp [flow])
        (by intros; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp (.push true) _) = _
      simp only [core_zero,core_update]
      simp only [product,BinaryData.encode,BinaryStack.applyOp,List.cons_append,List.append_assoc]
    have h₄ : Reaches (program F) (cfg F 4 (encode (product ea eb (a,b))++tail) [] out)
        (cfg F 1 (encode (ea (f (a,b)))++encode (listTree eb bs)++suffix) [] out)
        (F.limit (a,b)+1) := by
      intro bits
      simpa only [store,core,tail,List.append_assoc,cfg] using Flow.hop (flow F) 4 1 _ _ out bits _
        (F.correct (a,b) tail out bits) (by intros; rfl)
    exact (h₁.trans (h₂.trans (h₃.trans (h₄.trans (ih (f (a,b))))))).mono (by simp [time]; omega)

noncomputable def device {α β : Type} {ea : α → Data} {eb : β → Data} {f : α × β → α}
    (F : Device (product ea eb) ea f) :
    Device (product ea (listTree eb)) ea (fun z => fold f z.1 z.2) :=
  ofProgram _ _ _ (program F) (fun z => time F z.1 z.2+2) (by
    intro z suffix out bits
    have h₀ : Reaches (program F)
        ⟨some (program F).start,store (product ea (listTree eb) z) suffix,out⟩
        (cfg F 1 (encode (ea z.1)++encode (listTree eb z.2)++suffix) [] out) 2 := by
      intro bits
      apply Flow.hop_update (flow F) 0 1 _ _ _ out bits 1 .pop rfl (by intros; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
      simp only [flow,advance]
      simp only [product,BinaryData.encode,BinaryStack.applyOp,List.cons_append,List.append_assoc]
      funext i; fin_cases i <;> simp [store,core,BinaryData.encode,List.append_assoc]
    exact ((h₀.trans (loop F z.1 z.2 suffix out)).mono (by omega)).pad rfl bits)

end MeanPayoff.TreeDevice.Fold
end

end OAI

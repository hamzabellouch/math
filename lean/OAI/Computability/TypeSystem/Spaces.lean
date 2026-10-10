import Mathlib

namespace OAI

namespace PureTypeSystem

universe u

/-! Set-theoretic free observation spaces.
The four fixed sets are normal keys, tagged plain payloads, base observations,
and exit observations. The construction is independent of any typing choices. -/
namespace FreeObservations

variable (Q V B O : Type u)

inductive Payload (Y : Type u) : Type u
  | none : Payload Y
  | opposite : Y → Payload Y
  | plain : V → Payload Y

abbrev Frame (Y : Type u) : Type u := Q × Payload V Y
abbrev ContinueStack (Y : Type u) : Type u := List (Frame Q V Y)
abbrev ExitStack (Y : Type u) : Type u := ContinueStack Q V Y × Frame Q V Y

@[ext] structure Table (Y : Type u) : Type u where
  continuing : ContinueStack Q V Y → B
  exiting : ExitStack Q V Y → O

namespace Payload

variable {V : Type u} {X Y Z : Type u}

def map (f : X → Y) : Payload V X → Payload V Y
  | none => none
  | opposite x => opposite (f x)
  | plain v => plain v

@[simp] theorem map_id (p : Payload V X) : map id p = p := by cases p <;> rfl
@[simp] theorem map_comp (f : X → Y) (g : Y → Z) (p : Payload V X) :
    map g (map f p) = map (g ∘ f) p := by cases p <;> rfl

theorem map_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (map (V := V) f) := by
  intro p q he
  cases p <;> cases q <;> simp_all [map, hf.eq_iff]

theorem map_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (map (V := V) f) := by
  intro p
  cases p with
  | none => exact ⟨.none, rfl⟩
  | plain v => exact ⟨.plain v, rfl⟩
  | opposite y => obtain ⟨x, rfl⟩ := hf y; exact ⟨.opposite x, rfl⟩

end Payload

variable {Q V B O} {X Y Z : Type u}

def mapFrame (f : X → Y) (a : Frame Q V X) : Frame Q V Y :=
  (a.1, Payload.map f a.2)

def mapContinue (f : X → Y) : ContinueStack Q V X → ContinueStack Q V Y :=
  List.map (mapFrame f)

def mapExit (f : X → Y) (a : ExitStack Q V X) : ExitStack Q V Y :=
  (mapContinue f a.1, mapFrame f a.2)

@[simp] theorem mapFrame_id (a : Frame Q V X) : mapFrame id a = a := by
  cases a; simp [mapFrame]

@[simp] theorem mapFrame_comp (f : X → Y) (g : Y → Z) (a : Frame Q V X) :
    mapFrame g (mapFrame f a) = mapFrame (g ∘ f) a := by
  simp [mapFrame]

@[simp] theorem mapContinue_id (a : ContinueStack Q V X) : mapContinue id a = a := by
  induction a with
  | nil => rfl
  | cons a as ih => simpa only [mapContinue, List.map_cons, mapFrame_id] using congrArg (List.cons a) ih

@[simp] theorem mapContinue_comp (f : X → Y) (g : Y → Z) (a : ContinueStack Q V X) :
    mapContinue g (mapContinue f a) = mapContinue (g ∘ f) a := by
  simp only [mapContinue, List.map_map]
  congr 1
  funext a
  exact mapFrame_comp f g a

@[simp] theorem mapExit_id (a : ExitStack Q V X) : mapExit id a = a := by
  cases a; simp [mapExit]

@[simp] theorem mapExit_comp (f : X → Y) (g : Y → Z) (a : ExitStack Q V X) :
    mapExit g (mapExit f a) = mapExit (g ∘ f) a := by
  simp [mapExit]

theorem mapFrame_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (mapFrame (Q := Q) (V := V) f) := by
  intro p q he
  change (p.1, Payload.map f p.2) = (q.1, Payload.map f q.2) at he
  exact Prod.ext (congrArg (fun z : Q × Payload V Y => z.1) he)
    (Payload.map_injective hf (congrArg (fun z : Q × Payload V Y => z.2) he))

theorem mapFrame_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (mapFrame (Q := Q) (V := V) f) := by
  intro p
  obtain ⟨v, hv⟩ := Payload.map_surjective hf p.2
  exact ⟨(p.1,v), Prod.ext rfl hv⟩

theorem mapContinue_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (mapContinue (Q := Q) (V := V) f) :=
  List.map_injective_iff.mpr (mapFrame_injective hf)

theorem mapContinue_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (mapContinue (Q := Q) (V := V) f) :=
  List.map_surjective_iff.mpr (mapFrame_surjective hf)

theorem mapExit_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (mapExit (Q := Q) (V := V) f) := by
  intro p q he
  exact Prod.ext (mapContinue_injective hf (congrArg Prod.fst he))
    (mapFrame_injective hf (congrArg Prod.snd he))

theorem mapExit_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (mapExit (Q := Q) (V := V) f) := by
  intro p
  obtain ⟨s, hs⟩ := mapContinue_surjective hf p.1
  obtain ⟨a, ha⟩ := mapFrame_surjective hf p.2
  exact ⟨(s,a), Prod.ext hs ha⟩

namespace Table

def relabel (f : X → Y) (t : Table Q V B O Y) : Table Q V B O X where
  continuing := t.continuing ∘ mapContinue f
  exiting := t.exiting ∘ mapExit f

@[simp] theorem relabel_id (t : Table Q V B O X) : relabel id t = t := by
  ext <;> simp [relabel]

@[simp] theorem relabel_comp (f : X → Y) (g : Y → Z) (t : Table Q V B O Z) :
    relabel f (relabel g t) = relabel (g ∘ f) t := by
  ext <;> simp [relabel]

def default (b : B) (o : O) : Table Q V B O X where
  continuing := fun _ => b
  exiting := fun _ => o

@[simp] theorem relabel_default (f : X → Y) (b : B) (o : O) :
    relabel (Q := Q) (V := V) f (default b o) = default b o := rfl

theorem relabel_injective {f : X → Y} (hf : Function.Surjective f) :
    Function.Injective (relabel (Q := Q) (V := V) (B := B) (O := O) f) := by
  intro a b h
  apply Table.ext
  · funext s
    obtain ⟨t, rfl⟩ := mapContinue_surjective hf s
    exact congrFun (congrArg Table.continuing h) t
  · funext s
    obtain ⟨t, rfl⟩ := mapExit_surjective hf s
    exact congrFun (congrArg Table.exiting h) t

theorem relabel_surjective {f : X → Y} (hf : Function.Injective f) (b : B) (o : O) :
    Function.Surjective (relabel (Q := Q) (V := V) (B := B) (O := O) f) := by
  intro t
  obtain ⟨c, hc⟩ := (mapContinue_injective hf).surjective_comp_right' (fun _ => b) t.continuing
  obtain ⟨e, he⟩ := (mapExit_injective hf).surjective_comp_right' (fun _ => o) t.exiting
  exact ⟨⟨c,e⟩, Table.ext hc he⟩

/-- Exact factorization through a surjective payload map, simultaneously
at all finite lengths. No continuity/topology is assumed. -/
theorem relabel_range_iff {f : X → Y} (hf : Function.Surjective f) (t : Table Q V B O X) :
    (∃ s, relabel f s = t) ↔
      (∀ a b, mapContinue f a = mapContinue f b → t.continuing a = t.continuing b) ∧
      (∀ a b, mapExit f a = mapExit f b → t.exiting a = t.exiting b) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨fun _ _ he => congrArg s.continuing he, fun _ _ he => congrArg s.exiting he⟩
  · rintro ⟨hc, he⟩
    classical
    let c : ContinueStack Q V Y → ContinueStack Q V X := fun a => (mapContinue_surjective hf a).choose
    let e : ExitStack Q V Y → ExitStack Q V X := fun a => (mapExit_surjective hf a).choose
    have ch : ∀ a, mapContinue f (c a) = a := fun a => (mapContinue_surjective hf a).choose_spec
    have eh : ∀ a, mapExit f (e a) = a := fun a => (mapExit_surjective hf a).choose_spec
    refine ⟨⟨t.continuing ∘ c, t.exiting ∘ e⟩, ?_⟩
    apply Table.ext
    · funext a
      exact hc _ _ (ch _)
    · funext a
      exact he _ _ (eh _)

/-- Prefix a continue frame. Its slicing operation commutes with relabeling. -/
def slice (t : Table Q V B O X) (a : Frame Q V X) : Table Q V B O X where
  continuing := fun ns => t.continuing (a :: ns)
  exiting := fun ns => t.exiting (a :: ns.1, ns.2)

@[simp] theorem slice_relabel (f : X → Y) (t : Table Q V B O Y) (a : Frame Q V X) :
    (relabel f t).slice a = relabel f (t.slice (mapFrame f a)) := rfl

end Table

variable (Q V B O) in
@[reducible] def Stage : ℕ → Type u
  | 0 => PEmpty
  | n + 1 => Table Q V B O (Table Q V B O (Stage n))

variable (Q V B O) in
def step : ∀ n, Stage Q V B O n → Stage Q V B O (n + 1)
  | 0 => PEmpty.elim
  | n + 1 => Table.relabel (Table.relabel (step n))

variable (b : B) (o : O)

include b o in
theorem step_injective (n : ℕ) : Function.Injective (step Q V B O n) := by
  induction n with
  | zero => intro x; exact x.elim
  | succ n ih => exact Table.relabel_injective (Table.relabel_surjective ih b o)

variable (Q V B O) in
def inclusion (n m : ℕ) (h : n ≤ m) : Stage Q V B O n → Stage Q V B O m :=
  Nat.leRecOn h (fun {k} => step Q V B O k)

@[simp] theorem inclusion_self (n : ℕ) (x : Stage Q V B O n) :
    inclusion Q V B O n n le_rfl x = x := Nat.leRecOn_self x

@[simp] theorem inclusion_succ (n : ℕ) (x : Stage Q V B O n) :
    inclusion Q V B O n (n+1) (Nat.le_succ n) x = step Q V B O n x :=
  Nat.leRecOn_succ' x

theorem inclusion_trans {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (x : Stage Q V B O n) :
    inclusion Q V B O m k h' (inclusion Q V B O n m h x) =
      inclusion Q V B O n k (h.trans h') x := (Nat.leRecOn_trans h h' x).symm

instance stageDirectedSystem : DirectedSystem (Stage Q V B O) (inclusion Q V B O · · ·) where
  map_self := fun {_} x => inclusion_self _ x
  map_map := fun {_ _ _} h h' x => inclusion_trans h h' x

include b o in
theorem inclusion_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (inclusion Q V B O n m h) := by
  induction m, h using Nat.le_induction with
  | base => intro x y he; simpa only [inclusion_self] using he
  | succ m hm ih =>
    intro x y he
    simp only [inclusion, Nat.leRecOn_succ hm] at he
    exact ih (step_injective b o m he)

@[reducible] local instance functionFunLike (α β : Type u) : FunLike (α → β) α β where
  coe := fun f => f
  coe_injective := fun _ _ h => h

local instance stageCoeDirectedSystem : DirectedSystem (Stage Q V B O)
    (fun i j h => @DFunLike.coe (Stage Q V B O i → Stage Q V B O j) _ _
      (functionFunLike _ _) (inclusion Q V B O i j h)) := stageDirectedSystem

variable (Q V B O) in
abbrev Minus := DirectLimit (Stage Q V B O) (inclusion Q V B O)
variable (Q V B O) in
abbrev Plus := Table Q V B O (Minus Q V B O)

variable (Q V B O) in
def embed (n : ℕ) (x : Stage Q V B O n) : Minus Q V B O := ⟦⟨n,x⟩⟧

include b o in
theorem embed_injective (n : ℕ) : Function.Injective (embed Q V B O n) :=
  DirectLimit.mk_injective _ (fun _ _ h => inclusion_injective b o h) n

@[simp] theorem embed_inclusion {n m : ℕ} (h : n ≤ m) (x : Stage Q V B O n) :
    embed Q V B O m (inclusion Q V B O n m h x) = embed Q V B O n x :=
  DirectLimit.mk_apply n m x h

@[simp] theorem embed_step (n : ℕ) (x : Stage Q V B O n) :
    embed Q V B O (n+1) (step Q V B O n x) = embed Q V B O n x := by
  rw [← inclusion_succ]; exact embed_inclusion _ _

theorem exists_embed (x : Minus Q V B O) : ∃ n y, embed Q V B O n y = x := by
  obtain ⟨n,y,rfl⟩ := DirectLimit.exists_eq_mk _ x
  exact ⟨n,y,rfl⟩

theorem exists_embed_succ (x : Minus Q V B O) : ∃ n y, embed Q V B O (n+1) y = x := by
  obtain ⟨n,y,rfl⟩ := exists_embed x
  exact ⟨n, step Q V B O n y, embed_step n y⟩

variable (Q V B O) in
def restrict (n : ℕ) : Plus Q V B O → Table Q V B O (Stage Q V B O n) :=
  Table.relabel (embed Q V B O n)

include b o in
theorem restrict_surjective (n : ℕ) : Function.Surjective (restrict Q V B O n) :=
  Table.relabel_surjective (embed_injective b o n) b o

@[simp] theorem restrict_compat (n : ℕ) (p : Plus Q V B O) :
    Table.relabel (step Q V B O n) (restrict Q V B O (n+1) p) = restrict Q V B O n p := by
  rw [restrict, Table.relabel_comp]
  congr 1
  funext x
  exact embed_step n x

theorem restrict_inclusion {n m : ℕ} (h : n ≤ m) (p : Plus Q V B O) :
    Table.relabel (inclusion Q V B O n m h) (restrict Q V B O m p) = restrict Q V B O n p := by
  rw [restrict, Table.relabel_comp]
  congr 1
  funext x
  exact embed_inclusion h x

variable (Q V B O) in
def stageBehavior : ∀ n, Stage Q V B O n → Table Q V B O (Plus Q V B O)
  | 0 => PEmpty.elim
  | n+1 => Table.relabel (restrict Q V B O n)

include b o in
theorem stageBehavior_injective (n : ℕ) : Function.Injective (stageBehavior Q V B O n) := by
  cases n with
  | zero => intro x; exact x.elim
  | succ n => exact Table.relabel_injective (restrict_surjective b o n)

theorem stageBehavior_step (n : ℕ) (x : Stage Q V B O n) :
    stageBehavior Q V B O (n+1) (step Q V B O n x) = stageBehavior Q V B O n x := by
  cases n with
  | zero => exact x.elim
  | succ n =>
    change Table.relabel _ (Table.relabel _ x) = _
    rw [Table.relabel_comp]
    congr 1
    funext p
    exact restrict_compat n p

theorem stageBehavior_inclusion {n m : ℕ} (h : n ≤ m) (x : Stage Q V B O n) :
    stageBehavior Q V B O m (inclusion Q V B O n m h x) = stageBehavior Q V B O n x := by
  induction m, h using Nat.le_induction with
  | base => rw [inclusion_self]
  | succ m hm ih =>
    simp only [inclusion, Nat.leRecOn_succ hm, stageBehavior_step]
    exact ih

variable (Q V B O) in
def behavior : Minus Q V B O → Table Q V B O (Plus Q V B O) :=
  DirectLimit.lift (inclusion Q V B O) (stageBehavior Q V B O)
    (fun _ _ h x => (stageBehavior_inclusion h x).symm)

@[simp] theorem behavior_embed (n : ℕ) (x : Stage Q V B O n) :
    behavior Q V B O (embed Q V B O n x) = stageBehavior Q V B O n x := rfl

include b o in
theorem behavior_injective : Function.Injective (behavior Q V B O) :=
  DirectLimit.lift_injective _ _ _ (stageBehavior_injective b o)

variable (Q V) in
def plusDefault (b : B) (o : O) : Plus Q V B O := Table.default b o
variable (Q V) in
def minusDefault (b : B) (o : O) : Minus Q V B O :=
  embed Q V B O 1 (Table.default b o)

@[simp] theorem behavior_default :
    behavior Q V B O (minusDefault Q V b o) = Table.default b o := rfl

include b o in
/-- The finite bound is ONE stage for ALL finite input lengths. -/
theorem behavior_range_iff (t : Table Q V B O (Plus Q V B O)) :
    (∃ x, behavior Q V B O x = t) ↔ ∃ r,
      (∀ a a', mapContinue (restrict Q V B O r) a = mapContinue (restrict Q V B O r) a' →
        t.continuing a = t.continuing a') ∧
      (∀ a a', mapExit (restrict Q V B O r) a = mapExit (restrict Q V B O r) a' →
        t.exiting a = t.exiting a') := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨n,y,rfl⟩ := exists_embed_succ x
    exact ⟨n, (Table.relabel_range_iff (restrict_surjective b o n) _).mp ⟨y,rfl⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨y, hy⟩ := (Table.relabel_range_iff (restrict_surjective b o n) t).mpr hn
    exact ⟨embed Q V B O (n+1) y, hy⟩

/-- Slicing represented behaviors preserves the same finite stage. -/
theorem slice_range (x : Minus Q V B O) (a : Frame Q V (Plus Q V B O)) :
    ∃ y, behavior Q V B O y = (behavior Q V B O x).slice a := by
  obtain ⟨n,x,rfl⟩ := exists_embed_succ x
  refine ⟨embed Q V B O (n+1) (x.slice (mapFrame (restrict Q V B O n) a)), ?_⟩
  exact (Table.slice_relabel _ x a).symm

noncomputable def minusSlice (x : Minus Q V B O) (a : Frame Q V (Plus Q V B O)) : Minus Q V B O :=
  (slice_range x a).choose

@[simp] theorem behavior_minusSlice (x : Minus Q V B O) (a : Frame Q V (Plus Q V B O)) :
    behavior Q V B O (minusSlice x a) = (behavior Q V B O x).slice a := (slice_range x a).choose_spec

end FreeObservations

end PureTypeSystem

/-! Prefix observation spaces in the all-path plain construction.
Unrolling the exit spaces gives a single table of base observations.
Only domain feedback needs to be well founded; continuing paths themselves
may have arbitrary length and cycles. The required well-foundedness follows
from profile components and the syntax potential. -/

namespace PureTypeSystem.PlainSpaces
universe u

structure Schema (N : Type u) where
  Key : N → Type u
  target : (n : N) → Key n → N
  domain : (n : N) → Key n → Option N

namespace Schema
variable {N : Type u} (F : Schema N)

inductive Path : N → Type u
  | nil (n : N) : Path n
  | cons {n : N} (a : F.Key n) (p : Path (F.target n a)) : Path n

/-- The occurrence of a payload along a raw finite path. Certificates of a
particular domain introduce no computational information. -/
inductive Slot : {n : N} → F.Path n → N → Type u
  | head {n : N} {a : F.Key n} {p : F.Path (F.target n a)} {d : N}
      (h : F.domain n a = some d) : Slot (.cons a p) d
  | tail {n : N} {a : F.Key n} {p : F.Path (F.target n a)} {d : N}
      (s : Slot p d) : Slot (.cons a p) d

/-- A domain can be used after any finite number of continuation frames. -/
inductive Dependency : N → N → Prop
  | head {n : N} (a : F.Key n) {d : N} (h : F.domain n a = some d) : Dependency d n
  | tail {n d : N} (a : F.Key n) (h : Dependency d (F.target n a)) : Dependency d n

namespace Slot
variable {F}
theorem dependency {n d : N} {p : F.Path n} (s : F.Slot p d) : F.Dependency d n := by
  induction s with
  | head h => exact .head _ h
  | tail s ih => exact .tail _ ih
end Slot

abbrev Parameters (K : N → Type u) {n : N} (p : F.Path n) : Type u :=
  (d : N) → F.Slot p d → K d

abbrev FrameParameters (K : N → Type u) {n : N} (a : F.Key n) : Type u :=
  (d : N) → F.domain n a = some d → K d

abbrev Table (K : N → Type u) (B : Type u) (n : N) : Type u :=
  (p : F.Path n) → F.Parameters K p → B

noncomputable def Space (hw : WellFounded F.Dependency) (B : Type u) : N → Type u :=
  hw.fix fun n rec => (p : F.Path n) → ((d : N) → (s : F.Slot p d) → rec d s.dependency) → B

theorem space_eq (hw : WellFounded F.Dependency) (B : Type u) (n : N) :
    F.Space hw B n = F.Table (F.Space hw B) B n :=
  hw.fix_eq _ n

noncomputable def unfold (hw : WellFounded F.Dependency) (B : Type u) (n : N) :
    F.Space hw B n ≃ F.Table (F.Space hw B) B n :=
  Equiv.cast (F.space_eq hw B n)

namespace Parameters
variable {F} {K : N → Type u} {n : N}
def nil : F.Parameters K (.nil n) := fun _ s => nomatch s

def head {a : F.Key n} {p : F.Path (F.target n a)}
    (xs : F.Parameters K (.cons a p)) : F.FrameParameters K a :=
  fun _ h => xs _ (.head h)

def tail {a : F.Key n} {p : F.Path (F.target n a)}
    (xs : F.Parameters K (.cons a p)) : F.Parameters K p :=
  fun _ h => xs _ (.tail h)

def cons {a : F.Key n} {p : F.Path (F.target n a)}
    (x : F.FrameParameters K a) (xs : F.Parameters K p) : F.Parameters K (.cons a p)
  | _, .head h => x _ h
  | _, .tail s => xs _ s

@[simp] theorem head_cons {a : F.Key n} {p : F.Path (F.target n a)}
    (x : F.FrameParameters K a) (xs : F.Parameters K p) : (cons x xs).head = x := rfl
@[simp] theorem tail_cons {a : F.Key n} {p : F.Path (F.target n a)}
    (x : F.FrameParameters K a) (xs : F.Parameters K p) : (cons x xs).tail = xs := rfl
@[simp] theorem cons_head_tail {a : F.Key n} {p : F.Path (F.target n a)}
    (xs : F.Parameters K (.cons a p)) : cons xs.head xs.tail = xs := by
  funext d s
  cases s <;> rfl

theorem nil_unique (xs : F.Parameters K (.nil n)) : xs = nil := by
  funext d s
  cases s
end Parameters

/-- Splitting all-path tables at their first frame. -/
noncomputable def prefixEquiv (hw : WellFounded F.Dependency) (B : Type u) (n : N) :
    F.Space hw B n ≃ B × ((a : F.Key n) → F.FrameParameters (F.Space hw B) a →
      F.Space hw B (F.target n a)) where
  toFun t :=
    ⟨F.unfold hw B n t (.nil n) Parameters.nil,
     fun a x => (F.unfold hw B (F.target n a)).symm
       (fun p xs => F.unfold hw B n t (.cons a p) (Parameters.cons x xs))⟩
  invFun t := (F.unfold hw B n).symm (fun p xs => match p with
    | .nil _ => t.1
    | .cons a p => F.unfold hw B (F.target n a) (t.2 a xs.head) p xs.tail)
  left_inv t := by
    apply (F.unfold hw B n).injective
    simp only [Equiv.apply_symm_apply]
    funext p xs
    cases p with
    | nil n => rw [Parameters.nil_unique xs]
    | cons a p => simp only [Parameters.cons_head_tail]
  right_inv t := by
    apply Prod.ext
    · simp only [Equiv.apply_symm_apply]
    · funext a x
      apply (F.unfold hw B (F.target n a)).injective
      simp only [Equiv.apply_symm_apply]
      funext p xs
      rfl

/-- Constant tables give compatible distinguished parameters with no
additional choice of an inhabitant at any recursive node. -/
noncomputable def distinguished (hw : WellFounded F.Dependency) {B : Type u} (b : B) (n : N) :
    F.Space hw B n := (F.unfold hw B n).symm (fun _ _ => b)

@[simp] theorem distinguished_base (hw : WellFounded F.Dependency) {B : Type u}
    (b : B) (n : N) : (F.prefixEquiv hw B n (F.distinguished hw b n)).1 = b := by
  simp only [prefixEquiv, distinguished, Equiv.coe_fn_mk, Equiv.apply_symm_apply]

@[simp] theorem distinguished_next (hw : WellFounded F.Dependency) {B : Type u}
    (b : B) (n : N) (a : F.Key n) (x : F.FrameParameters (F.Space hw B) a) :
    (F.prefixEquiv hw B n (F.distinguished hw b n)).2 a x =
      F.distinguished hw b (F.target n a) := by
  simp only [prefixEquiv, distinguished, Equiv.coe_fn_mk, Equiv.apply_symm_apply]
end Schema
end PureTypeSystem.PlainSpaces

namespace PureTypeSystem.FreeObservations

universe u
variable {Q V B O : Type u}

/-- Membership in a specified finite minus stage, not just in the limit. -/
def InStage (n : ℕ) (x : Minus Q V B O) : Prop :=
  ∃ y : Stage Q V B O n, embed Q V B O n y = x

/-- The finite observation equivalence on unrestricted plus tables. -/
def Agree (n : ℕ) (p q : Plus Q V B O) : Prop :=
  restrict Q V B O n p = restrict Q V B O n q

namespace InStage

theorem mono {n m : ℕ} (h : n ≤ m) {x : Minus Q V B O} (hx : InStage n x) :
    InStage m x := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨inclusion Q V B O n m h y, embed_inclusion h y⟩

theorem not_zero (x : Minus Q V B O) : ¬ InStage 0 x := by
  rintro ⟨a, _⟩
  exact a.elim

theorem exists_stage (x : Minus Q V B O) : ∃ n, InStage n x :=
  exists_embed x

end InStage

namespace Agree

theorem mono {n m : ℕ} (h : n ≤ m) {p q : Plus Q V B O} (hpq : Agree m p q) :
    Agree n p q := by
  unfold Agree at *
  rw [← restrict_inclusion h p, ← restrict_inclusion h q, hpq]

theorem refl (n : ℕ) (p : Plus Q V B O) : Agree n p p := rfl

theorem symm {n : ℕ} {p q : Plus Q V B O} (h : Agree n p q) : Agree n q p := Eq.symm h

theorem trans {n : ℕ} {p q r : Plus Q V B O}
    (h : Agree n p q) (h' : Agree n q r) : Agree n p r := Eq.trans h h'

end Agree

/-- Exact characterization at a specified stage, used for the uniform
bound at a minus lambda. -/
theorem inStage_succ_iff (b : B) (o : O) (n : ℕ) (x : Minus Q V B O) :
    InStage (n+1) x ↔
      (∀ a a', mapContinue (restrict Q V B O n) a = mapContinue (restrict Q V B O n) a' →
          (behavior Q V B O x).continuing a = (behavior Q V B O x).continuing a') ∧
      (∀ a a', mapExit (restrict Q V B O n) a = mapExit (restrict Q V B O n) a' →
          (behavior Q V B O x).exiting a = (behavior Q V B O x).exiting a') := by
  constructor
  · rintro ⟨y, rfl⟩
    exact (Table.relabel_range_iff (restrict_surjective b o n) _).mp ⟨y, rfl⟩
  · intro h
    obtain ⟨y, hy⟩ := (Table.relabel_range_iff (restrict_surjective b o n) _).mpr h
    exact ⟨y, behavior_injective b o (by exact hy)⟩

/-- A table with the uniform finite invariance is represented at exactly the
promised next stage. This is stronger than mere totality in the colimit. -/
theorem exists_inStage_behavior (b : B) (o : O) (n : ℕ)
    (t : Table Q V B O (Plus Q V B O))
    (hc : ∀ a a', mapContinue (restrict Q V B O n) a = mapContinue (restrict Q V B O n) a' →
      t.continuing a = t.continuing a')
    (he : ∀ a a', mapExit (restrict Q V B O n) a = mapExit (restrict Q V B O n) a' →
      t.exiting a = t.exiting a') :
    ∃ x, InStage (n+1) x ∧ behavior Q V B O x = t := by
  obtain ⟨y, hy⟩ := (Table.relabel_range_iff (restrict_surjective b o n) t).mpr ⟨hc, he⟩
  exact ⟨embed Q V B O (n+1) y, ⟨y, rfl⟩, hy⟩

/-- Slicing remains in the same finite minus stage. -/
theorem inStage_minusSlice (b : B) (o : O) {n : ℕ} {x : Minus Q V B O} (hx : InStage n x)
    (a : Frame Q V (Plus Q V B O)) : InStage n (minusSlice x a) := by
  cases n with
  | zero => exact False.elim (InStage.not_zero x hx)
  | succ n =>
      obtain ⟨y, rfl⟩ := hx
      refine ⟨y.slice (mapFrame (restrict Q V B O n) a), ?_⟩
      apply behavior_injective b o
      rw [behavior_minusSlice]
      exact (Table.slice_relabel _ y a).symm

/-- A raw lambda table. Its body is selected by a continuing first frame;
its exit operation is selected by the unique terminal frame. Gates and
invalid-frame defaults can be included in these two functions. -/
def lambdaTable (base : B)
    (body : Frame Q V (Plus Q V B O) → Minus Q V B O)
    (exit : Frame Q V (Plus Q V B O) → O) : Table Q V B O (Plus Q V B O) where
  continuing
    | [] => base
    | a :: as => (behavior Q V B O (body a)).continuing as
  exiting
    | ([], a) => exit a
    | (a :: as, e) => (behavior Q V B O (body a)).exiting (as, e)

/-- The representability step at a minus lambda. The finite level is uniform
across *all* first frames and all stack lengths, not a pointwise bound. -/
theorem lambdaTable_representable (b : B) (o : O) (n : ℕ) (base : B)
    (body : Frame Q V (Plus Q V B O) → Minus Q V B O)
    (exit : Frame Q V (Plus Q V B O) → O)
    (hb : ∀ a, InStage (n+1) (body a))
    (hc : ∀ a a', mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a' →
      body a = body a')
    (he : ∀ a a', mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a' →
      exit a = exit a') :
    ∃ x, InStage (n+1) x ∧ behavior Q V B O x = lambdaTable base body exit := by
  apply exists_inStage_behavior b o n
  · intro as as' ha
    cases as with
    | nil =>
        cases as' with
        | nil => rfl
        | cons a as' => cases ha
    | cons a as =>
        cases as' with
        | nil => cases ha
        | cons a' as' =>
            have hh := List.cons.inj ha
            change (behavior Q V B O (body a)).continuing as =
              (behavior Q V B O (body a')).continuing as'
            rw [← hc a a' hh.1]
            exact ((inStage_succ_iff b o n (body a)).mp (hb a)).1 as as' hh.2
  · rintro ⟨as,e⟩ ⟨as',e'⟩ ha
    have hh := Prod.mk.inj ha
    cases as with
    | nil =>
        cases as' with
        | nil => exact he e e' hh.2
        | cons a as' => cases hh.1
    | cons a as =>
        cases as' with
        | nil => cases hh.1
        | cons a' as' =>
            have hs := List.cons.inj hh.1
            change (behavior Q V B O (body a)).exiting (as,e) =
              (behavior Q V B O (body a')).exiting (as',e')
            rw [← hc a a' hs.1]
            apply ((inStage_succ_iff b o n (body a)).mp (hb a)).2
            exact Prod.ext hs.2 hh.2

def FrameBound (n : Nat) (a : Frame Q V (Minus Q V B O)) : Prop :=
  ∀ x, a.2 = .opposite x → InStage n x

def ContinueBound (n : Nat) (as : ContinueStack Q V (Minus Q V B O)) : Prop :=
  ∀ a ∈ as, FrameBound n a

def ExitBound (n : Nat) (a : ExitStack Q V (Minus Q V B O)) : Prop :=
  ContinueBound n a.1 ∧ FrameBound n a.2

namespace FrameBound
variable {n m : Nat} {a : Frame Q V (Minus Q V B O)}
theorem mono (h : n ≤ m) (ha : FrameBound n a) : FrameBound m a :=
  fun x hx => (ha x hx).mono h

theorem exists_preimage (ha : FrameBound n a) :
    ∃ a' : Frame Q V (Stage Q V B O n), mapFrame (embed Q V B O n) a' = a := by
  rcases a with ⟨q,p⟩
  cases p with
  | none => exact ⟨(q,.none),rfl⟩
  | plain v => exact ⟨(q,.plain v),rfl⟩
  | opposite x =>
      obtain ⟨y,hy⟩ := ha x rfl
      exact ⟨(q,.opposite y), congrArg (fun x => (q,Payload.opposite x)) hy⟩

theorem embed (n : Nat) (a : Frame Q V (Stage Q V B O n)) :
    FrameBound n (mapFrame (FreeObservations.embed Q V B O n) a) := by
  rcases a with ⟨q,p⟩
  cases p with
  | none => intro x h; cases h
  | plain v => intro x h; cases h
  | opposite x =>
      intro y hy
      have he : FreeObservations.embed Q V B O n x = y := Payload.opposite.inj hy
      exact ⟨x,he⟩
end FrameBound

namespace ContinueBound
variable {n m : Nat} {as : ContinueStack Q V (Minus Q V B O)}
theorem mono (h : n ≤ m) (ha : ContinueBound n as) : ContinueBound m as :=
  fun a hm => (ha a hm).mono h

theorem exists_preimage (ha : ContinueBound n as) :
    ∃ as' : ContinueStack Q V (Stage Q V B O n), mapContinue (embed Q V B O n) as' = as := by
  induction as with
  | nil => exact ⟨[],rfl⟩
  | cons a as ih =>
      obtain ⟨a',ha'⟩ := (ha a (List.mem_cons_self)).exists_preimage
      obtain ⟨as',has'⟩ := ih (fun a h => ha a (List.mem_cons_of_mem _ h))
      exact ⟨a' :: as', congrArg₂ List.cons ha' has'⟩

theorem embed (n : Nat) (as : ContinueStack Q V (Stage Q V B O n)) :
    ContinueBound n (mapContinue (FreeObservations.embed Q V B O n) as) := by
  intro a ha
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  exact FrameBound.embed n x

theorem cons (a : Frame Q V (Minus Q V B O)) (ha : FrameBound n a)
    (has : ContinueBound n as) : ContinueBound n (a :: as) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  · exact has x hx
end ContinueBound

namespace Agree
variable {n m : Nat} {p q : Plus Q V B O}
theorem continuing (h : Agree n p q) {as : ContinueStack Q V (Minus Q V B O)}
    (ha : ContinueBound n as) : p.continuing as = q.continuing as := by
  obtain ⟨as',rfl⟩ := ha.exists_preimage
  exact congrArg (fun t : Table Q V B O (Stage Q V B O n) => t.continuing as') h

theorem exiting (h : Agree n p q) {as : ExitStack Q V (Minus Q V B O)}
    (ha : ExitBound n as) : p.exiting as = q.exiting as := by
  obtain ⟨as',has'⟩ := ha.1.exists_preimage
  obtain ⟨a',ha'⟩ := ha.2.exists_preimage
  have hh := congrArg (fun t : Table Q V B O (Stage Q V B O n) => t.exiting (as',a')) h
  change p.exiting (mapContinue _ as',mapFrame _ a') = q.exiting (mapContinue _ as',mapFrame _ a') at hh
  simpa only [has',ha'] using hh

theorem of_observations
    (hc : ∀ as, ContinueBound n as → p.continuing as = q.continuing as)
    (he : ∀ as, ExitBound n as → p.exiting as = q.exiting as) : Agree n p q := by
  apply Table.ext
  · funext as
    exact hc _ (ContinueBound.embed n as)
  · funext as
    exact he _ ⟨ContinueBound.embed n as.1,FrameBound.embed n as.2⟩

theorem slice (h : Agree n p q) (hmn : m ≤ n)
    (a : Frame Q V (Minus Q V B O)) (ha : FrameBound n a) : Agree m (p.slice a) (q.slice a) := by
  apply of_observations
  · intro as has
    exact h.continuing (ContinueBound.cons a ha (has.mono hmn))
  · intro as has
    exact h.exiting ⟨ContinueBound.cons a ha (has.1.mono hmn),has.2.mono hmn⟩

theorem all_levels_eq (h : ∀ n, Agree n p q) : p = q := by
  have bound_frame (a : Frame Q V (Minus Q V B O)) : ∃ n, FrameBound n a := by
    rcases a with ⟨key,payload⟩
    cases payload with
    | none => exact ⟨0, fun _ hh => by cases hh⟩
    | plain v => exact ⟨0, fun _ hh => by cases hh⟩
    | opposite x =>
        obtain ⟨n,hn⟩ := InStage.exists_stage x
        exact ⟨n,fun y hy => Payload.opposite.inj hy ▸ hn⟩
  have bound_stack (as : ContinueStack Q V (Minus Q V B O)) : ∃ n, ContinueBound n as := by
    induction as with
    | nil => exact ⟨0, fun _ hh => by cases hh⟩
    | cons a as ih =>
        obtain ⟨n,hn⟩ := bound_frame a
        obtain ⟨m,hm⟩ := ih
        exact ⟨max n m,ContinueBound.cons a (hn.mono (le_max_left _ _)) (hm.mono (le_max_right _ _))⟩
  apply Table.ext
  · funext as
    obtain ⟨n,hn⟩ := bound_stack as
    exact (h n).continuing hn
  · funext as
    obtain ⟨n,hn⟩ := bound_stack as.1
    obtain ⟨m,hm⟩ := bound_frame as.2
    exact (h (max n m)).exiting ⟨hn.mono (le_max_left _ _),hm.mono (le_max_right _ _)⟩
end Agree

variable (b : B) (o : O)
include b o

theorem minusSlice_eq_of_restrict {n : Nat} {x : Minus Q V B O} (hx : InStage (n+1) x)
    {a a' : Frame Q V (Plus Q V B O)}
    (ha : mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a') :
    minusSlice x a = minusSlice x a' := by
  apply behavior_injective b o
  rw [behavior_minusSlice,behavior_minusSlice]
  apply Table.ext
  · funext as
    apply ((inStage_succ_iff b o n x).mp hx).1
    exact congrArg (fun a => a :: mapContinue (restrict Q V B O n) as) ha
  · funext as
    apply ((inStage_succ_iff b o n x).mp hx).2
    exact Prod.ext (congrArg (fun a => a :: mapContinue (restrict Q V B O n) as.1) ha) rfl

theorem minusExit_eq_of_restrict {n : Nat} {x : Minus Q V B O} (hx : InStage (n+1) x)
    {a a' : Frame Q V (Plus Q V B O)}
    (ha : mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a') :
    (behavior Q V B O x).exiting ([],a) = (behavior Q V B O x).exiting ([],a') := by
  apply ((inStage_succ_iff b o n x).mp hx).2
  exact Prod.ext rfl ha

omit b o

/-- The unrestricted plus-side analogue of the minus lambda table. -/
def plusLambdaTable (base : B) (body : Frame Q V (Minus Q V B O) → Plus Q V B O)
    (exit : Frame Q V (Minus Q V B O) → O) : Plus Q V B O where
  continuing
    | [] => base
    | a :: as => (body a).continuing as
  exiting
    | ([],a) => exit a
    | (a :: as,e) => (body a).exiting (as,e)

theorem plusLambdaTable_agree {n : Nat} (base : B)
    (body body' : Frame Q V (Minus Q V B O) → Plus Q V B O)
    (exit exit' : Frame Q V (Minus Q V B O) → O)
    (hb : ∀ a, FrameBound n a → Agree n (body a) (body' a))
    (he : ∀ a, FrameBound n a → exit a = exit' a) :
    Agree n (plusLambdaTable base body exit) (plusLambdaTable base body' exit') := by
  apply Agree.of_observations
  · intro as has
    cases as with
    | nil => rfl
    | cons a as =>
        exact (hb a (has a List.mem_cons_self)).continuing (fun x hx => has x (List.mem_cons_of_mem _ hx))
  · rintro ⟨as,e⟩ ⟨has,hes⟩
    cases as with
    | nil => exact he e hes
    | cons a as =>
        exact (hb a (has a List.mem_cons_self)).exiting
          ⟨fun x hx => has x (List.mem_cons_of_mem _ hx),hes⟩
end PureTypeSystem.FreeObservations

end OAI

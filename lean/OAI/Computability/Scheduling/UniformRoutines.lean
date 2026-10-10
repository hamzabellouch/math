import OAI.Computability.Scheduling.Realizers

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26

section

namespace ThreeMachine.StackCompiler
variable {α : Type u1} {β : Type u2} [Coding α] [Coding β]

theorem volume_pos (x : α) : 0 < volume x := by
  change 0 < (enc x).encode.length
  cases enc x <;> simp [Data.encode]

theorem volume_le_cons (a : α) (xs : List α) : volume xs ≤ volume (a :: xs) := by
  rw [volume_cons]; omega

theorem volume_list_member {xs : List α} {a : α} (h : a ∈ xs) : volume a ≤ volume xs := by
  induction xs with
  | nil => simp at h
  | cons b xs ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · rw [volume_cons]; omega
    · exact le_trans (ih hm) (volume_le_cons b xs)

theorem volume_list_le (xs : List α) (M : ℕ) (h : ∀ a ∈ xs, volume a ≤ M) :
    volume xs ≤ xs.length*(M+1)+1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [volume_cons,List.length_cons]
    nlinarith

theorem length_le_volume (xs : List α) : xs.length ≤ volume xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [volume_cons,List.length_cons]; omega

namespace Realizer
variable {F : α × β → β}

theorem foldTime_bound (R : Realizer F) (I : β → Prop) (A T X : ℕ)
    (xs : List α) (b : β) (hb : I b) (hX : volume xs ≤ X)
    (hA : ∀ b, I b → volume b ≤ A)
    (hs : ∀ a ∈ xs, ∀ b, I b → I (F (a,b)))
    (hT : ∀ a ∈ xs, ∀ b, I b → R.time (a,b) ≤ T) :
    foldTime R b xs ≤ xs.length*(T+20*(X+2*A+1))+1 := by
  induction xs generalizing b with
  | nil => simp [foldTime]
  | cons a xs ih =>
    have ha : a ∈ a :: xs := by simp
    have hb' := hs a ha b hb
    have hstep := hT a ha b hb
    have hvol := hA b hb
    have hvol' := hA (F (a,b)) hb'
    have htail := ih (F (a,b)) hb' (le_trans (volume_le_cons a xs) hX)
      (fun a ha => hs a (by simp [ha])) (fun a ha => hT a (by simp [ha]))
    simp only [foldTime,List.length_cons]
    nlinarith

end Realizer
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Realizer
variable {α : Type u3} {β : Type u4} {γ : Type u5} [Coding α] [Coding β] [Coding γ]

def onFst {f : α → β} (R : Realizer f) : Realizer (fun x : α × γ => (f x.1,x.2)) :=
  (fst.comp R).pair snd

def onSnd {f : α → β} (R : Realizer f) : Realizer (fun x : γ × α => (x.1,f x.2)) :=
  fst.pair (snd.comp R)

def swap : Realizer (fun x : α × β => (x.2,x.1)) := snd.pair fst

omit [Coding α] in
theorem fold_cons_eq (xs ys : List α) :
    xs.foldl (fun ys a => a :: ys) ys = xs.reverse ++ ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih => simp [ih,List.append_assoc]

def reverse : Realizer (fun xs : List α => xs.reverse) :=
  ((id.pair (nil : Realizer (fun _ : List α => ([] : List α)))).comp cons.fold).congr
    (fun xs => by simp only [Function.comp_apply,fold_cons_eq,List.append_nil,id_eq])

def mapBody {f : α × γ → β} (R : Realizer f) :
    Realizer (fun x : α × (γ × List β) => (x.2.1,f (x.1,x.2.1) :: x.2.2)) :=
  (snd.comp fst).pair ((((fst.pair (snd.comp fst)).comp R).pair (snd.comp snd)).comp cons)

omit [Coding α] [Coding β] [Coding γ] in
theorem map_fold_eq (f : α × γ → β) (xs : List α) (e : γ) (ys : List β) :
    xs.foldl (fun s a => (s.1,f (a,s.1) :: s.2)) (e,ys) =
      (e,(xs.map (fun a => f (a,e))).reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih => simp [ih,List.append_assoc]

def map {f : α × γ → β} (R : Realizer f) :
    Realizer (fun x : List α × γ => x.1.map (fun a => f (a,x.2))) :=
  (((fst.pair (snd.pair nil)).comp (mapBody R).fold).comp (snd.comp reverse)).congr (fun x => by
    simp only [Function.comp_apply,map_fold_eq,List.append_nil,List.reverse_reverse])

end ThreeMachine.StackCompiler.Realizer

namespace ThreeMachine.StackCompiler

structure Uniform {I : Type u6} {α : I → Type u7} {β : I → Type u8} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
    (f : ∀ i, α i → β i) where
  transform : Data → Data
  charge : Data → ℕ
  routine : Routine transform charge
  correct : ∀ i x, transform (enc x) = enc (f i x)

namespace Uniform
variable {I : Type u9} {α : I → Type u10} {β : I → Type u11} {γ : I → Type u12} {δ : I → Type u13}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)] [∀ i, Coding (δ i)]
variable {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}

def specialize (R : Uniform f) (i : I) : Realizer (f i) :=
  ⟨R.transform,R.charge,R.routine,R.correct i⟩

def time (R : Uniform f) (i : I) (x : α i) : ℕ := R.charge (enc x)

def id : Uniform (fun (i : I) (x : α i) => x) :=
  ⟨_root_.id,_,Routine.identity,fun _ _ => rfl⟩

def unit : Uniform (fun (i : I) (_ : α i) => ()) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def nil : Uniform (fun (i : I) (_ : α i) => ([] : List (β i))) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def zero : Uniform (fun (i : I) (_ : α i) => (0 : ℕ)) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def false : Uniform (fun (i : I) (_ : α i) => Bool.false) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def comp (R : Uniform f) (S : Uniform g) : Uniform (fun i => g i ∘ f i) where
  transform := S.transform ∘ R.transform
  charge := _
  routine := R.routine.comp S.routine
  correct i x := by simp only [Function.comp_apply,R.correct,S.correct]

def pair {g : ∀ i, α i → γ i} (R : Uniform f) (S : Uniform g) :
    Uniform (fun i x => (f i x,g i x)) where
  transform := fun x => .pair (R.transform x) (S.transform x)
  charge := _
  routine := R.routine.pair S.routine
  correct i x := by simp only [R.correct,S.correct,enc_pair]

def fst : Uniform (fun (i : I) => (Prod.fst : α i × β i → α i)) :=
  ⟨Data.head,_,Routine.select true,fun _ _ => rfl⟩

def snd : Uniform (fun (i : I) => (Prod.snd : α i × β i → β i)) :=
  ⟨Data.tail,_,Routine.select Bool.false,fun _ _ => rfl⟩

def congr {f' : ∀ i, α i → β i} (R : Uniform f) (h : ∀ i x, f i x = f' i x) : Uniform f' :=
  { R with correct := fun i x => (R.correct i x).trans (congrArg enc (h i x)) }

def reinterpret (f : ∀ i, α i → β i) (h : ∀ i x, enc (f i x) = enc x) : Uniform f :=
  ⟨_root_.id,_,Routine.identity,fun i x => (h i x).symm⟩

def fold {F : ∀ i, α i × β i → β i} (R : Uniform F) :
    Uniform (fun i (x : List (α i) × β i) => x.1.foldl (fun b a => F i (a,b)) x.2) where
  transform := fun x => Data.fold R.transform x.tail x.head
  charge := _
  routine := R.routine.fold
  correct i x := (R.specialize i).fold_correct x.1 x.2

def choose {g : ∀ i, α i → β i} (R : Uniform f) (S : Uniform g) :
    Uniform (fun i (x : Bool × α i) => if x.1 then f i x.2 else g i x.2) where
  transform := fun x => if x.head.nonempty then ((snd (α := fun _ : I => Bool) (β := α)).comp R).transform x else ((snd (α := fun _ : I => Bool) (β := α)).comp S).transform x
  charge := _
  routine := ((snd (α := fun _ : I => Bool) (β := α)).comp R).routine.choose ((snd (α := fun _ : I => Bool) (β := α)).comp S).routine
  correct i x := ((R.specialize i).choose (S.specialize i)).correct x

def ite {p : ∀ i, α i → Bool} {g : ∀ i, α i → β i}
    (P : Uniform p) (R : Uniform f) (S : Uniform g) :
    Uniform (fun i x => if p i x then f i x else g i x) :=
  ((P.pair id).comp (R.choose S)).congr (fun _ _ => rfl)

def cons : Uniform (fun (i : I) (x : α i × List (α i)) => x.1 :: x.2) := reinterpret _ (fun _ _ => rfl)

def onFst (R : Uniform f) : Uniform (fun i (x : α i × γ i) => (f i x.1,x.2)) :=
  (fst.comp R).pair snd

def onSnd (R : Uniform f) : Uniform (fun i (x : γ i × α i) => (x.1,f i x.2)) :=
  fst.pair (snd.comp R)

def reverse : Uniform (fun (i : I) (xs : List (α i)) => xs.reverse) :=
  ((id.pair (nil : Uniform (fun (i : I) (_ : List (α i)) => ([] : List (α i))))).comp cons.fold).congr
    (fun _ _ => by simp only [Function.comp_apply,Realizer.fold_cons_eq,List.append_nil])

def mapBody {f : ∀ i, α i × γ i → β i} (R : Uniform f) :
    Uniform (fun i (x : α i × (γ i × List (β i))) => (x.2.1,f i (x.1,x.2.1) :: x.2.2)) :=
  (snd.comp fst).pair ((((fst.pair (snd.comp fst)).comp R).pair (snd.comp snd)).comp cons)

def map {f : ∀ i, α i × γ i → β i} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.map (fun a => f i (a,x.2))) :=
  (((fst.pair (snd.pair nil)).comp (mapBody R).fold).comp (snd.comp reverse)).congr (fun _ _ => by
    simp only [Function.comp_apply,Realizer.map_fold_eq,List.append_nil,List.reverse_reverse])

end Uniform

namespace Realizer
variable {α : Type u14} {β : Type u15} [Coding α] [Coding β] {f : α → β}
def uniform (R : Realizer f) (I : Type u16) : Uniform (fun (_ : I) => f) :=
  ⟨R.transform,R.charge,R.routine,fun _ => R.correct⟩
end Realizer

end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Realizer
variable {α : Type u17} [Coding α]

def test (p : α → Bool) (h : ∀ x, (enc x).nonempty = p x) : Realizer p where
  transform := fun x => if x.nonempty then .pair .nil .nil else .nil
  charge := _
  routine := (Routine.identity.pair Routine.nil).comp
    ((Routine.constant (.pair .nil .nil)).choose Routine.nil)
  correct x := by rw [h]; cases p x <;> rfl

def not : Realizer Bool.not :=
  ((id.pair unit).comp ((false : Realizer (fun _ : Unit => Bool.false)).choose (constant true))).congr
    (fun b => by cases b <;> rfl)

def and : Realizer (fun x : Bool × Bool => x.1 && x.2) :=
  (id.choose false).congr (fun x => by rcases x with ⟨a,b⟩; cases a <;> rfl)

def or : Realizer (fun x : Bool × Bool => x.1 || x.2) :=
  ((constant true).choose id).congr (fun x => by rcases x with ⟨a,b⟩; cases a <;> rfl)

def positive : Realizer (fun n : ℕ => decide (0 < n)) :=
  test _ (by intro n; cases n <;> rfl)

def isZero : Realizer (fun n : ℕ => decide (n = 0)) :=
  (positive.comp not).congr (fun n => by cases n <;> rfl)

def pred : Realizer Nat.pred :=
  ⟨Data.tail,_,Routine.select Bool.false,fun n => by cases n <;> rfl⟩

theorem encode_replicate_unit (n : ℕ) : enc (List.replicate n ()) = enc n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,enc_cons,enc_unit,ih,enc_succ]

def unroll : Realizer (fun n : ℕ => List.replicate n ()) :=
  reinterpret _ encode_replicate_unit

omit [Coding α] in
theorem fold_replicate (f : α → α) (n : ℕ) (a : α) :
    (List.replicate n ()).foldl (fun a _ => f a) a = f^[n] a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.foldl_cons,Function.iterate_succ_apply] using ih (f a)

def iterate {f : α → α} (R : Realizer f) : Realizer (fun x : ℕ × α => f^[x.1] x.2) :=
  (unroll.onFst.comp (snd.comp R).fold).congr (fun x => fold_replicate f x.1 x.2)

theorem iterate_pred (n m : ℕ) : Nat.pred^[n] m = m-n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,ih,Nat.pred_eq_sub_one]; omega

theorem iterate_succ (n m : ℕ) : (fun k : ℕ => k+1)^[n] m = m+n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,ih]; omega

def add : Realizer (fun x : ℕ × ℕ => x.1+x.2) :=
  succ.iterate.congr (fun x => by rw [iterate_succ,Nat.add_comm])

def sub : Realizer (fun x : ℕ × ℕ => x.1-x.2) :=
  (swap.comp pred.iterate).congr (fun x => iterate_pred x.2 x.1)

def le : Realizer (fun x : ℕ × ℕ => decide (x.1 ≤ x.2)) :=
  (sub.comp isZero).congr (fun x => by simp only [Function.comp_apply,Nat.sub_eq_zero_iff_le])

def eqNat : Realizer (fun x : ℕ × ℕ => decide (x.1 = x.2)) :=
  ((le.pair (swap.comp le)).comp and).congr (fun x => by
    apply Bool.eq_iff_iff.mpr
    simp [le_antisymm_iff])

end Realizer
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u18} {α : I → Type u19} {β : I → Type u20} {γ : I → Type u21}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

def test (p : ∀ i, α i → Bool) (h : ∀ i x, (enc x).nonempty = p i x) : Uniform p where
  transform := fun x => if x.nonempty then .pair .nil .nil else .nil
  charge := _
  routine := (Routine.identity.pair Routine.nil).comp
    ((Routine.constant (.pair .nil .nil)).choose Routine.nil)
  correct i x := by rw [h]; cases p i x <;> rfl

def isCons : Uniform (fun (i : I) (xs : List (α i)) => !xs.isEmpty) :=
  test _ (by intro _ xs; cases xs <;> rfl)

def head? : Uniform (fun (i : I) (xs : List (α i)) => xs.head?) where
  transform := fun x => if x.nonempty then .pair x.head .nil else .nil
  charge := _
  routine := (Routine.identity.pair Routine.nil).comp
    ((((Routine.select true).comp (Routine.select true)).pair Routine.nil).choose Routine.nil)
  correct i xs := by cases xs <;> rfl

def swap : Uniform (fun (i : I) (x : α i × β i) => (x.2,x.1)) := snd.pair fst

def append : Uniform (fun (i : I) (x : List (α i) × List (α i)) => x.1 ++ x.2) :=
  (((fst.comp reverse).pair snd).comp cons.fold).congr (fun _ _ => by
    simp only [Function.comp_apply,Realizer.fold_cons_eq,List.reverse_reverse])

omit [∀ i, Coding (α i)] in
theorem fold_append_eq (i : I) (xs : List (List (α i))) (acc : List (α i)) :
    xs.foldl (fun ys zs => ys ++ zs) acc = acc ++ xs.flatten := by
  induction xs generalizing acc with
  | nil => simp
  | cons xs xss ih => simp [ih,List.append_assoc]

omit [∀ i, Coding (α i)] in
theorem flatten_fold_eq (i : I) (xs : List (List (α i))) (acc : List (α i)) :
    xs.foldl (fun ys zs => zs.foldl (fun ys a => a :: ys) ys) acc = xs.flatten.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons xs xss ih =>
    rw [List.foldl_cons,ih,Realizer.fold_cons_eq]
    simp only [List.flatten_cons,List.reverse_append,List.append_assoc]

def flatten : Uniform (fun (i : I) (xs : List (List (α i))) => xs.flatten) :=
  (((id.pair nil).comp cons.fold.fold).comp reverse).congr (fun _ _ => by
    simp only [Function.comp_apply,flatten_fold_eq,List.append_nil,List.reverse_reverse])

def flatMap {f : ∀ i, α i × γ i → List (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.flatMap (fun a => f i (a,x.2))) :=
  (R.map.comp flatten).congr (fun _ _ => rfl)

def filterBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : α i × (γ i × List (α i))) =>
      (x.2.1,if p i (x.1,x.2.1) then x.1 :: x.2.2 else x.2.2)) :=
  (snd.comp fst).pair
    (((fst.pair (snd.comp fst)).comp P).ite ((fst.pair (snd.comp snd)).comp cons) (snd.comp snd))

omit [∀ i, Coding (α i)] [∀ i, Coding (γ i)] in
theorem filter_fold_eq (p : ∀ i, α i × γ i → Bool) (i : I)
    (xs : List (α i)) (e : γ i) (ys : List (α i)) :
    xs.foldl (fun s a => (s.1,if p i (a,s.1) then a :: s.2 else s.2)) (e,ys) =
      (e,(xs.filter (fun a => p i (a,e))).reverse ++ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases he : p i (a,e) <;> simp [he,ih,List.append_assoc]

def filter {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.filter (fun a => p i (a,x.2))) :=
  (((fst.pair (snd.pair nil)).comp (filterBody P).fold).comp (snd.comp reverse)).congr (fun _ _ => by
    simp only [Function.comp_apply,filter_fold_eq,List.append_nil,List.reverse_reverse])

def optionToList : Uniform (fun (i : I) (x : Option (α i)) => x.toList) :=
  reinterpret _ (by intro i x; cases x <;> rfl)

def filterMap {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.filterMap (fun a => f i (a,x.2))) :=
  (R.comp optionToList).flatMap.congr (fun i x => by
    induction x.1 with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.flatMap_cons,List.filterMap_cons]
      cases he : f i (a,x.2) <;> simp_all)

def optionMap {f : ∀ i, α i × γ i → β i} (R : Uniform f) :
    Uniform (fun i (x : Option (α i) × γ i) => x.1.map (fun a => f i (a,x.2))) :=
  ((optionToList.onFst.comp R.map).comp head?).congr (fun i x => by
    rcases x with ⟨o,e⟩
    cases o <;> rfl)

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u22} {α : I → Type u23} {β : I → Type u24} {γ : I → Type u25}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

def constant {δ : Type u26} [Coding δ] (a : δ) :
    Uniform (fun (i : I) (_ : α i) => a) where
  transform := fun _ => enc a
  charge := _
  routine := Routine.constant (enc a)
  correct _ _ := rfl

def some : Uniform (fun (i : I) (a : α i) => Option.some a) where
  transform := fun x => .pair x .nil
  charge := _
  routine := Routine.identity.pair Routine.nil
  correct _ _ := rfl

def none : Uniform (fun (i : I) (_ : α i) => (Option.none : Option (β i))) :=
  ⟨fun _ => .nil,_,Routine.nil,fun _ _ => rfl⟩

def optionIsSome : Uniform (fun (i : I) (x : Option (α i)) => x.isSome) :=
  test _ (by intro _ x; cases x <;> rfl)

def getD : Uniform (fun (i : I) (x : Option (α i) × α i) => x.1.getD x.2) :=
  (((fst.comp optionToList).pair snd).comp fst.fold).congr (fun _ x => by
    rcases x with ⟨o,a⟩; cases o <;> rfl)

def length : Uniform (fun (i : I) (xs : List (α i)) => xs.length) :=
  ((id.pair zero).comp (snd.comp (Realizer.succ.uniform I)).fold).congr (fun i xs => by
    have h : ∀ (ys : List (α i)) (n : ℕ),
        ys.foldl (fun n _ => n+1) n = n+ys.length := by
      intro ys; induction ys with
      | nil => intro n; simp
      | cons a ys ih => intro n; simp [ih]; omega
    simpa only [Function.comp_apply,Nat.zero_add] using h xs 0)

def iterate {f : ∀ i, α i → α i} (R : Uniform f) :
    Uniform (fun i (x : ℕ × α i) => (f i)^[x.1] x.2) :=
  ((Realizer.unroll.uniform I).onFst.comp (snd.comp R).fold).congr (fun i x =>
    Realizer.fold_replicate (f i) x.1 x.2)

def anyBody {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : α i × (γ i × Bool)) =>
      (x.2.1,x.2.2 || p i (x.1,x.2.1))) :=
  (snd.comp fst).pair
    (((snd.comp snd).pair ((fst.pair (snd.comp fst)).comp P)).comp (Realizer.or.uniform I))

omit [∀ i, Coding (α i)] [∀ i, Coding (γ i)] in
theorem any_fold_eq (p : ∀ i, α i × γ i → Bool) (i : I)
    (xs : List (α i)) (e : γ i) (b : Bool) :
    xs.foldl (fun s a => (s.1,s.2 || p i (a,s.1))) (e,b) =
      (e,b || xs.any (fun a => p i (a,e))) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih => simp [ih,Bool.or_assoc]

def any {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.any (fun a => p i (a,x.2))) :=
  (((fst.pair (snd.pair false)).comp (anyBody P).fold).comp snd).congr (fun _ _ => by
    simp only [Function.comp_apply,any_fold_eq,Bool.false_or])

def all {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.all (fun a => p i (a,x.2))) :=
  ((P.comp (Realizer.not.uniform I)).any.comp (Realizer.not.uniform I)).congr (fun _ x => by
    simp only [Function.comp_apply,List.all_eq_not_any_not])

def find? {p : ∀ i, α i × γ i → Bool} (P : Uniform p) :
    Uniform (fun i (x : List (α i) × γ i) => x.1.find? (fun a => p i (a,x.2))) :=
  (P.filter.comp head?).congr (fun _ x => by
    dsimp only [Function.comp_apply]
    induction x.1 with
    | nil => rfl
    | cons a xs ih => cases he : p _ (a,x.2) <;> simp_all)

def firstResult {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) => (x.1.filterMap (fun a => f i (a,x.2))).head?) :=
  R.filterMap.comp head?

def tableOf {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : List (α i) × γ i) =>
      x.1.filterMap (fun a => (f i (a,x.2)).map (fun b => (a,b)))) :=
  ((R.pair fst).comp ((swap : Uniform (fun i (x : β i × α i) => (x.2,x.1))).optionMap)).filterMap

end ThreeMachine.StackCompiler.Uniform

end

end OAI

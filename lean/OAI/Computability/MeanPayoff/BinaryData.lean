import OAI.Computability.MeanPayoff.ArithmeticBounds

namespace OAI

section

namespace MeanPayoff.WorkStack.RegisterCompile

theorem signed_adds (a b : Bool) (xs ys out : List Bool) (bits : ℕ → Bool) :
    RegisterBits.advance (program SignedAddition.program) bits
      (lift SignedAddition.program out (SignedAddition.state .start (a::xs) (b::ys) []))
      (6*(2*max xs.length ys.length+5)) =
      lift SignedAddition.program out (SignedAddition.stopped
        ((SignedBits.add a b false xs ys).sign::(SignedBits.add a b false xs ys).digits) []) := by
  rw [advance_six, SignedAddition.program_adds]
end MeanPayoff.WorkStack.RegisterCompile
namespace MeanPayoff.BinaryData

def boolData : Bool → Data
  | false => .nil
  | true => .pair .nil .nil

def listData : List Bool → Data
  | [] => .nil
  | b :: bs => .pair (boolData b) (listData bs)

def wordData (w : SignedBits.Word) : Data := listData (w.sign :: w.digits)

def consCode : Bool → List Bool
  | false => [true, false]
  | true => [true, true, false, false]

@[simp] theorem encode_list_nil : encode (listData []) = [false] := rfl
@[simp] theorem encode_list_cons (b : Bool) (bs : List Bool) :
    encode (listData (b :: bs)) = consCode b ++ encode (listData bs) := by cases b <;> rfl

@[simp] theorem consCode_length_le (b : Bool) : (consCode b).length ≤ 4 := by cases b <;> decide

def feedCost : List Bool → ℕ
  | [] => 0
  | b :: bs => (consCode b).length + 1 + feedCost bs

@[simp] theorem feedCost_append (a b : List Bool) : feedCost (a ++ b) = feedCost a + feedCost b := by
  induction a with
  | nil => simp [feedCost]
  | cons x xs ih => simp only [List.cons_append, feedCost, ih]; omega

@[simp] theorem feedCost_reverse (a : List Bool) : feedCost a.reverse = feedCost a := by
  induction a with
  | nil => rfl
  | cons b bs ih => simp only [List.reverse_cons, feedCost_append, ih, feedCost]; omega

theorem feedCost_le (a : List Bool) : feedCost a ≤ 5*a.length := by
  induction a with
  | nil => rfl
  | cons b bs ih => have := consCode_length_le b; simp only [feedCost, List.length_cons]; omega

theorem encode_list_length_le (a : List Bool) : (encode (listData a)).length ≤ 4*a.length+1 := by
  induction a with
  | nil => simp
  | cons b bs ih =>
    simp only [encode_list_cons, List.length_append, List.length_cons]
    have := consCode_length_le b; omega

namespace Unbox
open RegisterBits
open BinaryStack (applyOp)
open Take (config_ext advance_front advance_add)

inductive Label where
  | read | bit | skip0 | skip1 | push (b : Bool) | restore | put (b : Bool)
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem decode (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply q

noncomputable def program : Program 3 where
  states := Fintype.card Label
  start := enc .read
  read q := match equiv.symm q with
    | .read | .bit | .skip0 | .skip1 => 0
    | .push _ | .restore => 2
    | .put _ => 1
  transition q top _ := match equiv.symm q with
    | .read => top.map fun b => ⟨enc (if b then .bit else .restore), .pop, none⟩
    | .bit => top.map fun b => ⟨enc (if b then .skip0 else .push false), .pop, none⟩
    | .skip0 => some ⟨enc .skip1, .pop, none⟩
    | .skip1 => some ⟨enc (.push true), .pop, none⟩
    | .push b => some ⟨enc .read, .push b, none⟩
    | .restore => top.map fun b => ⟨enc (.put b), .pop, none⟩
    | .put b => some ⟨enc .restore, .push b, none⟩

noncomputable def cfg (q : Label) (xs ys zs out : List Bool) : Config program :=
  ⟨some (enc q), ![xs,ys,zs], out⟩
def stopped (xs ys out : List Bool) : Config program := ⟨none, ![xs,ys,[]], out⟩

@[simp] theorem read_nil (xs ys zs out : List Bool) (b : Bool) :
    RegisterBits.step program (cfg .read (false::xs) ys zs out) b = cfg .restore xs ys zs out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl

theorem feed_one (b : Bool) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .read (consCode b ++ xs) ys zs out)
      ((consCode b).length + 1) = cfg .read xs ys (b::zs) out := by
  cases b <;>
    apply config_ext <;>
    simp [advance, RegisterBits.step, cfg, program, consCode, applyOp]
  all_goals funext i; fin_cases i <;> rfl

theorem feeds (bs xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .read (encode (listData bs) ++ xs) ys zs out)
      (feedCost bs) = cfg .read (false::xs) ys (bs.reverse ++ zs) out := by
  induction bs generalizing zs bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [encode_list_cons, List.append_assoc, feedCost]
    rw [advance_add, feed_one, ih]
    simp [List.reverse_cons, List.append_assoc]

@[simp] theorem restore_read (b : Bool) (xs ys zs out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg .restore xs ys (b::zs) out) coin = cfg (.put b) xs ys zs out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl
@[simp] theorem restore_put (b : Bool) (xs ys zs out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg (.put b) xs ys zs out) coin = cfg .restore xs (b::ys) zs out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl
@[simp] theorem restore_done (xs ys out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg .restore xs ys [] out) coin = stopped xs ys out := by
  simp [RegisterBits.step, cfg, program, stopped]

theorem restores (zs xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .restore xs ys zs out) (2*zs.length+1) =
      stopped xs (zs.reverse ++ ys) out := by
  induction zs generalizing ys bits with
  | nil => simp [advance]
  | cons b zs ih =>
    rw [show 2*(b::zs).length+1 = (2*zs.length+1+1)+1 by simp; omega,
      Take.advance_front, restore_read, Take.advance_front, restore_put, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem read_nil_advance (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .read (false::xs) ys zs out) 1 = cfg .restore xs ys zs out := by
  simp only [advance, read_nil]

theorem unboxes (bs xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .read (encode (listData bs) ++ xs) ys [] out)
      (feedCost bs+1+(2*bs.length+1)) = stopped xs (bs++ys) out := by
  rw [advance_add _ _ _ (feedCost bs+1) (2*bs.length+1),
    advance_add _ _ _ (feedCost bs) 1, feeds]
  simp only [List.append_nil, read_nil_advance]
  rw [show bs.length = bs.reverse.length by simp, restores]
  simp

theorem unboxes_bound (bs : List Bool) : feedCost bs+1+(2*bs.length+1) ≤ 7*bs.length+2 := by
  have := feedCost_le bs; omega

end Unbox
end MeanPayoff.BinaryData
namespace MeanPayoff.BinaryData.Box
open RegisterBits
open BinaryStack (applyOp)
open Take (config_ext advance_add)

inductive Label where
  | reverse | revPut (b : Bool) | init | feed | zero | one0 | one1 | one2 | last
  deriving DecidableEq, Fintype
noncomputable def equiv : Label ≃ Fin (Fintype.card Label) := Fintype.equivFin _
noncomputable def enc (q : Label) := equiv q
@[simp] theorem decode (q : Label) : equiv.symm (enc q) = q := equiv.symm_apply_apply q

noncomputable def program : Program 3 where
  states := Fintype.card Label
  start := enc .reverse
  read q := match equiv.symm q with
    | .reverse => 0
    | .revPut _ | .feed => 2
    | _ => 1
  transition q top _ := match equiv.symm q with
    | .reverse => some (match top with
        | none => ⟨enc .init, .keep, none⟩
        | some b => ⟨enc (.revPut b), .pop, none⟩)
    | .revPut b => some ⟨enc .reverse, .push b, none⟩
    | .init => some ⟨enc .feed, .push false, none⟩
    | .feed => top.map fun b => ⟨enc (if b then .one0 else .zero), .pop, none⟩
    | .zero => some ⟨enc .last, .push false, none⟩
    | .one0 => some ⟨enc .one1, .push false, none⟩
    | .one1 => some ⟨enc .one2, .push false, none⟩
    | .one2 => some ⟨enc .last, .push true, none⟩
    | .last => some ⟨enc .feed, .push true, none⟩

noncomputable def cfg (q : Label) (xs ys zs out : List Bool) : Config program :=
  ⟨some (enc q), ![xs,ys,zs], out⟩
def stopped (ys out : List Bool) : Config program := ⟨none, ![[],ys,[]], out⟩

@[simp] theorem reverse_read (b : Bool) (xs ys zs out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg .reverse (b::xs) ys zs out) coin = cfg (.revPut b) xs ys zs out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl
@[simp] theorem reverse_put (b : Bool) (xs ys zs out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg (.revPut b) xs ys zs out) coin = cfg .reverse xs ys (b::zs) out := by
  apply config_ext <;> simp [RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl

theorem reverses (bs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .reverse bs ys zs out) (2*bs.length) =
      cfg .reverse [] ys (bs.reverse++zs) out := by
  induction bs generalizing zs bits with
  | nil => rfl
  | cons b bs ih =>
    rw [show 2*(b::bs).length = (2*bs.length+1)+1 by simp; omega,
      Take.advance_front, reverse_read, Take.advance_front, reverse_put, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem initializes (ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .reverse [] ys zs out) 2 = cfg .feed [] (false::ys) zs out := by
  apply config_ext <;> simp [advance, RegisterBits.step, cfg, program, applyOp]
  funext i; fin_cases i <;> rfl

theorem feed_one (b : Bool) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .feed xs ys (b::zs) out) ((consCode b).length+1) =
      cfg .feed xs (consCode b++ys) zs out := by
  cases b <;>
    apply config_ext <;>
    simp [advance, RegisterBits.step, cfg, program, consCode, applyOp]
  all_goals funext i; fin_cases i <;> rfl

theorem feeds (bs acc xs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .feed xs (encode (listData acc)++ys) bs out) (feedCost bs) =
      cfg .feed xs (encode (listData (bs.reverse++acc))++ys) [] out := by
  induction bs generalizing acc bits with
  | nil => rfl
  | cons b bs ih =>
    rw [feedCost, advance_add, feed_one]
    rw [← List.append_assoc, ← encode_list_cons, ih]
    simp [List.reverse_cons, List.append_assoc]

@[simp] theorem feed_done (ys out : List Bool) (coin : Bool) :
    RegisterBits.step program (cfg .feed [] ys [] out) coin = stopped ys out := by
  simp [RegisterBits.step, cfg, program, stopped]

theorem boxes (bs ys out : List Bool) (bits : ℕ → Bool) :
    advance program bits (cfg .reverse bs ys [] out)
      (2*bs.length+2+feedCost bs+1) = stopped (encode (listData bs)++ys) out := by
  rw [advance_add _ _ _ (2*bs.length+2+feedCost bs) 1,
    advance_add _ _ _ (2*bs.length+2) (feedCost bs),
    advance_add _ _ _ (2*bs.length) 2, reverses]
  simp only [List.append_nil]
  rw [initializes]
  change advance _ _ (advance _ _ (cfg .feed [] (encode (listData [])++ys) bs.reverse out) _) 1 = _
  rw [← feedCost_reverse bs, feeds]
  simp [advance]

theorem boxes_bound (bs : List Bool) : 2*bs.length+2+feedCost bs+1 ≤ 7*bs.length+3 := by
  have := feedCost_le bs; omega

end MeanPayoff.BinaryData.Box
namespace MeanPayoff.RegisterBits.Flow
open BinaryData.Take (advance_add)

theorem hop {K : ℕ} (P : Program K) (p q : Fin P.nodes) (s t : Fin K → List Bool)
    (out : List Bool) (bits : ℕ → Bool) (N : ℕ)
    (hm : advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N = ⟨none,t,out⟩)
    (hn : ∀ top bit, P.next p top bit = some ⟨q, .keep, none⟩) :
    ∃ d ≤ N+1, advance (compile P) bits (state P p s out) d = state P q t out := by
  obtain ⟨d, hd, he⟩ := macro_runs P p s out bits N (by rw [hm])
  rw [hm] at he
  refine ⟨d+1, by omega, ?_⟩
  simp only [advance, he, step_boundary, hn]
  simp [BinaryStack.applyOp]

theorem finish {K : ℕ} (P : Program K) (p : Fin P.nodes) (s t : Fin K → List Bool)
    (out : List Bool) (bits : ℕ → Bool) (N : ℕ)
    (hm : advance (P.block p) bits ⟨some (P.block p).start, s, out⟩ N = ⟨none,t,out⟩)
    (hn : ∀ top bit, P.next p top bit = none) :
    ∃ d ≤ N+1, advance (compile P) bits (state P p s out) d = ⟨none,t,out⟩ := by
  obtain ⟨d, hd, he⟩ := macro_runs P p s out bits N (by rw [hm])
  rw [hm] at he
  refine ⟨d+1, by omega, ?_⟩
  simp only [advance, he, step_boundary, hn]
end MeanPayoff.RegisterBits.Flow
end

end OAI

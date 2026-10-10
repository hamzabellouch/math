import OAI.Computability.MeanPayoff.Packets

namespace OAI

section

namespace MeanPayoff
namespace RegisterBits
open BinaryStack (Op applyOp)

structure Act (s : ℕ) where
  next : Fin s
  work : Op
  emit : Option Bool
structure Program (K : ℕ) where
  states : ℕ
  start : Fin states
  read : Fin states → Fin K
  transition : Fin states → Option Bool → Bool → Option (Act states)
structure Config {K : ℕ} (P : Program K) where
  control : Option (Fin P.states)
  stack : Fin K → List Bool
  output : List Bool

def step {K : ℕ} (P : Program K) (c : Config P) (bit : Bool) : Config P :=
  match c.control with
  | none => c
  | some q =>
    match P.transition q (c.stack (P.read q)).head? bit with
    | none => {c with control := none}
    | some a => ⟨some a.next, Function.update c.stack (P.read q) (applyOp a.work (c.stack (P.read q))),
        c.output ++ a.emit.toList⟩

def encode : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encode bs

def encodeAll : List (List Bool) → List Bool
  | [] => []
  | bs :: bss => encode bs ++ encodeAll bss

@[simp] theorem encode_length (bs : List Bool) : (encode bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [encode, ih]; omega

@[simp] theorem encodeAll_append (a b : List (List Bool)) :
    encodeAll (a ++ b) = encodeAll a ++ encodeAll b := by
  induction a with
  | nil => rfl
  | cons xs a ih => simp [encodeAll, ih, List.append_assoc]

@[simp] theorem encodeAll_length (bss : List (List Bool)) :
    (encodeAll bss).length = 2 * (bss.map List.length).sum + bss.length := by
  induction bss with
  | nil => rfl
  | cons bs bss ih => simp only [encodeAll, List.length_append, encode_length, List.map_cons,
      List.sum_cons, List.length_cons, ih]; omega

namespace Compile
inductive Label (s K : ℕ) where
  | initMove
  | initPad (left : Fin (K + 1))
  | initRestore
  | initTag
  | source (q : Fin s)
  | seek (q : Fin s) (bit : Bool) (left : Fin (K + 1))
  | payload (q : Fin s) (bit : Bool)
  | skip (q : Fin s) (bit : Bool) (left : Fin (K + 1))
  | pushOne (dest : Option (Fin s)) (b : Bool)
  | pushTwo (dest : Option (Fin s)) (b c : Bool)
  | restore (dest : Option (Fin s))
  | halt
  deriving DecidableEq, Fintype

noncomputable def equiv (s K : ℕ) : Label s K ≃ Fin (Fintype.card (Label s K)) := Fintype.equivFin _
noncomputable def enc {s K : ℕ} (q : Label s K) := equiv s K q
@[simp] theorem decode {s K : ℕ} (q : Label s K) : (equiv s K).symm (enc q) = q :=
  (equiv s K).symm_apply_apply _

noncomputable def dispatch {K : ℕ} (P : Program K) (q : Fin P.states) (bit : Bool)
    (top : Option Bool) : BinaryStack.Act (Fintype.card (Label P.states K)) :=
  let instruction := P.transition q top bit
  let dest := instruction.map Act.next
  let op := instruction.map Act.work |>.getD .keep
  let emit := instruction.bind Act.emit
  match top, op with
  | none, .keep | none, .pop => ⟨enc (.restore dest), ![.keep, .keep], emit⟩
  | none, .push b => ⟨enc (.pushOne dest true), ![.push b, .keep], emit⟩
  | some _, .keep => ⟨enc (.restore dest), ![.push true, .keep], emit⟩
  | some _, .pop => ⟨enc (.restore dest), ![.pop, .keep], emit⟩
  | some _, .push b => ⟨enc (.pushTwo dest b true), ![.push true, .keep], emit⟩

noncomputable def program {K : ℕ} (P : Program K) : BinaryStack.Program where
  states := Fintype.card (Label P.states K)
  start := enc .initMove
  transition q top bit :=
    match (equiv P.states K).symm q with
    | .initMove =>
      match top 0 with
      | some b => some ⟨enc .initMove, ![.pop, .push b], none⟩
      | none => some ⟨enc (.initPad ⟨K, by omega⟩), ![.keep, .keep], none⟩
    | .initPad left =>
      if h : left.val = 0 then some ⟨enc .initRestore, ![.keep, .keep], none⟩
      else some ⟨enc (.initPad ⟨left.val - 1, by omega⟩), ![.push false, .keep], none⟩
    | .initRestore =>
      match top 1 with
      | some b => some ⟨enc .initTag, ![.push b, .pop], none⟩
      | none => some ⟨enc (.source P.start), ![.keep, .keep], none⟩
    | .initTag => some ⟨enc .initRestore, ![.push true, .keep], none⟩
    | .source q => some ⟨enc (.seek q bit ⟨(P.read q).val, by omega⟩), ![.keep, .keep], none⟩
    | .seek q coin left =>
      if h : left.val = 0 then
        match top 0 with
        | some false => some (dispatch P q coin none)
        | some true => some ⟨enc (.payload q coin), ![.pop, .keep], none⟩
        | none => some ⟨enc .halt, ![.keep, .keep], none⟩
      else
        match top 0 with
        | some false => some ⟨enc (.seek q coin ⟨left.val - 1, by omega⟩), ![.pop, .push false], none⟩
        | some true => some ⟨enc (.skip q coin left), ![.pop, .push true], none⟩
        | none => some ⟨enc .halt, ![.keep, .keep], none⟩
    | .skip q coin left =>
      match top 0 with
      | some b => some ⟨enc (.seek q coin left), ![.pop, .push b], none⟩
      | none => some ⟨enc .halt, ![.keep, .keep], none⟩
    | .payload q coin =>
      match top 0 with
      | some b => some (dispatch P q coin (some b))
      | none => some ⟨enc .halt, ![.keep, .keep], none⟩
    | .pushOne dest b => some ⟨enc (.restore dest), ![.push b, .keep], none⟩
    | .pushTwo dest b c => some ⟨enc (.pushOne dest c), ![.push b, .keep], none⟩
    | .restore dest =>
      match top 1 with
      | some b => some ⟨enc (.restore dest), ![.push b, .pop], none⟩
      | none => dest.map fun q => ⟨enc (.source q), ![.keep, .keep], none⟩
    | .halt => none

end Compile
end RegisterBits
end MeanPayoff

namespace MeanPayoff.RegisterBits.Compile
open BinaryStack (advance)

noncomputable def cfg {K : ℕ} (P : Program K) (q : Label P.states K)
    (xs ys out : List Bool) : BinaryStack.Config (program P) :=
  ⟨some (enc q), ![xs, ys], out⟩

theorem advance_add (P : BinaryStack.Program) (bits : ℕ → Bool)
    (c : BinaryStack.Config P) (a b : ℕ) :
    advance P bits c (a + b) =
      advance P (fun j => bits (a + j)) (advance P bits c a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change BinaryStack.step P (advance P bits c (a + b)) (bits (a + b)) = _
    rw [ih]
    rfl

@[simp] theorem step_skip {K : ℕ} (P : Program K) (q : Fin P.states)
    (coin bit b : Bool) (left : Fin (K + 1)) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.skip q coin left) (b :: xs) ys out) bit =
      cfg P (.seek q coin left) xs (b :: ys) out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, BinaryStack.applyOp]
  · simp [BinaryStack.step, cfg, program]

@[simp] theorem step_seek_tag {K : ℕ} (P : Program K) (q : Fin P.states)
    (coin bit : Bool) (left : Fin (K + 1)) (h : left.val ≠ 0) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.seek q coin left) (true :: xs) ys out) bit =
      cfg P (.skip q coin left) xs (true :: ys) out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program, h]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, h, BinaryStack.applyOp]
  · simp [BinaryStack.step, cfg, program, h]

@[simp] theorem step_seek_delim {K : ℕ} (P : Program K) (q : Fin P.states)
    (coin bit : Bool) (left : Fin (K + 1)) (h : left.val ≠ 0) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.seek q coin left) (false :: xs) ys out) bit =
      cfg P (.seek q coin ⟨left.val - 1, by omega⟩) xs (false :: ys) out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program, h]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, h, BinaryStack.applyOp]
  · simp [BinaryStack.step, cfg, program, h]

theorem seek_one {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool)
    (left : Fin (K + 1)) (h : left.val ≠ 0) (xs tail ys out : List Bool) (bits : ℕ → Bool) :
    advance (program P) bits (cfg P (.seek q coin left) (encode xs ++ tail) ys out)
        (encode xs).length =
      cfg P (.seek q coin ⟨left.val - 1, by omega⟩) tail ((encode xs).reverse ++ ys) out := by
  induction xs generalizing ys bits with
  | nil => simpa only [encode, List.singleton_append, List.length_singleton, advance,
      List.reverse_singleton] using step_seek_delim P q coin (bits 0) left h tail ys out
  | cons b xs ih =>
    simp only [encode, List.cons_append, List.length_cons]
    rw [BinaryStack.advance_front, step_seek_tag P q coin _ left h,
      BinaryStack.advance_front, step_skip]
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem seek_prefix {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool)
    (prefx : List (List Bool)) (hp : prefx.length ≤ K) (tail ys out : List Bool)
    (bits : ℕ → Bool) :
    advance (program P) bits
      (cfg P (.seek q coin ⟨prefx.length, by omega⟩) (encodeAll prefx ++ tail) ys out)
      (encodeAll prefx).length =
      cfg P (.seek q coin 0) tail ((encodeAll prefx).reverse ++ ys) out := by
  induction prefx generalizing ys bits with
  | nil => simp [encodeAll, advance]
  | cons xs pref ih =>
    simp only [List.length_cons, encodeAll, List.length_append]
    rw [List.append_assoc, advance_add, seek_one P q coin _ (by simp)]
    simp only [List.length_cons] at hp
    have he : (⟨pref.length + 1 - 1, by omega⟩ : Fin (K + 1)) =
        ⟨pref.length, by omega⟩ := by
      apply Fin.ext; simp
    rw [he, ih (by omega)]
    simp [List.reverse_append, List.append_assoc]

@[simp] theorem step_restore_some {K : ℕ} (P : Program K) (dest : Option (Fin P.states))
    (bit b : Bool) (xs ys out : List Bool) :
    BinaryStack.step (program P) (cfg P (.restore dest) xs (b :: ys) out) bit =
      cfg P (.restore dest) (b :: xs) ys out := by
  apply BinaryStack.Config.ext
  · simp [BinaryStack.step, cfg, program]
  · funext i; fin_cases i <;> simp [BinaryStack.step, cfg, program, BinaryStack.applyOp]
  · simp [BinaryStack.step, cfg, program]

noncomputable def sourceCfg {K : ℕ} (P : Program K) (dest : Option (Fin P.states))
    (xs ys out : List Bool) : BinaryStack.Config (program P) :=
  ⟨dest.map (fun q => enc (.source q)), ![xs, ys], out⟩

@[simp] theorem step_restore_nil {K : ℕ} (P : Program K) (dest : Option (Fin P.states))
    (bit : Bool) (xs out : List Bool) :
    BinaryStack.step (program P) (cfg P (.restore dest) xs [] out) bit =
      sourceCfg P dest xs [] out := by
  cases dest <;> apply BinaryStack.Config.ext
  all_goals first
    | solve | simp [BinaryStack.step, cfg, sourceCfg, program]
    | solve | funext i; fin_cases i <;> simp [BinaryStack.step, cfg, sourceCfg, program, BinaryStack.applyOp]

theorem restore_all {K : ℕ} (P : Program K) (dest : Option (Fin P.states))
    (xs ys out : List Bool) (bits : ℕ → Bool) :
    advance (program P) bits (cfg P (.restore dest) xs ys out) (ys.length + 1) =
      sourceCfg P dest (ys.reverse ++ xs) [] out := by
  induction ys generalizing xs bits with
  | nil => simp [advance]
  | cons b ys ih =>
    rw [List.length_cons, BinaryStack.advance_front, step_restore_some, ih]
    simp [List.reverse_cons, List.append_assoc]

end MeanPayoff.RegisterBits.Compile

namespace MeanPayoff.RegisterBits.Compile
open BinaryStack (advance applyOp)

def localOp {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool) (xs : List Bool) :=
  ((P.transition q xs.head? coin).map Act.work).getD .keep

def localDest {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool) (xs : List Bool) :=
  (P.transition q xs.head? coin).map Act.next

def localEmit {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool) (xs : List Bool) :=
  (P.transition q xs.head? coin).bind Act.emit

theorem local_update {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool)
    (xs tail ys out : List Bool) :
    ∃ n, 1 ≤ n ∧ n ≤ 4 ∧ ∀ bits : ℕ → Bool,
      advance (program P) bits (cfg P (.seek q coin 0) (encode xs ++ tail) ys out) n =
        cfg P (.restore (localDest P q coin xs))
          (encode (applyOp (localOp P q coin xs) xs) ++ tail) ys
          (out ++ (localEmit P q coin xs).toList) := by
  cases xs with
  | nil =>
    cases he : P.transition q none coin with
    | none =>
      refine ⟨1, by omega, by omega, ?_⟩
      intro bits
      apply BinaryStack.Config.ext
      all_goals first
        | solve | simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
        | solve | funext i; fin_cases i <;> simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
    | some a =>
      obtain ⟨dest, op, emit⟩ := a
      cases op with
      | keep =>
        refine ⟨1, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
      | pop =>
        refine ⟨1, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
      | push b =>
        refine ⟨2, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
  | cons b xs =>
    cases he : P.transition q (some b) coin with
    | none =>
      refine ⟨2, by omega, by omega, ?_⟩
      intro bits
      apply BinaryStack.Config.ext
      all_goals first
        | solve | simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
        | solve | funext i; fin_cases i <;> simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
    | some a =>
      obtain ⟨dest, op, emit⟩ := a
      cases op with
      | keep =>
        refine ⟨2, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
      | pop =>
        refine ⟨2, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
      | push x =>
        refine ⟨4, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]

end MeanPayoff.RegisterBits.Compile
end

end OAI

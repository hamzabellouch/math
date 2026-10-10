import Mathlib
import OAI.Probability.Contingency.IntegerDrawTail

namespace OAI

/-! Stack Safety. -/

noncomputable section


namespace Contingency.BitModel.StackCode
noncomputable section

theorem mass_eq_zero_of_safe (P : Program) (xs : List Bool) (Safe : List Bool→Prop)
    (hs : ∀ (t : ℕ) (f : Fin t→Bool),(run P xs f).state=none → Safe (run P xs f).memory.outputRev.reverse)
    (out : List Bool) (ho : ¬Safe out) (t : ℕ) : mass P xs out t=0 := by
  classical
  unfold mass
  have he : (Finset.univ.filter fun f : Fin t→Bool => (run P xs f).state=none ∧
      (run P xs f).memory.outputRev.reverse=out)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro f _ hh
    apply ho
    rw [← hh.2]
    exact hs t f hh.1
  rw [he]
  simp

theorem safe_compile (P : Program) (xs : List Bool) (Safe : List Bool→Prop)
    (hs : ∀ (t : ℕ) (f : Fin t→Bool),(run P xs f).state=none → Safe (run P xs f).memory.outputRev.reverse)
    (t : ℕ) (f : Fin t→Bool) (hh : ((compile P).run xs f).state=none) :
    Safe ((compile P).run xs f).outputRev.reverse := by
  classical
  by_contra hn
  have hm := mass_compile_all P xs ((compile P).run xs f).outputRev.reverse t
  rw [mass_eq_zero_of_safe P xs Safe hs _ hn] at hm
  have hc : 0<(Finset.univ.filter fun g : Fin t→Bool => ((compile P).run xs g).state=none ∧
      ((compile P).run xs g).outputRev.reverse=((compile P).run xs f).outputRev.reverse).card := by
    apply Finset.card_pos.mpr
    exact ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh,rfl⟩⟩
  have hp : 0<(compile P).mass xs ((compile P).run xs f).outputRev.reverse t := by
    unfold Machine.mass
    apply div_pos _ (by positivity)
    exact_mod_cast hc
  linarith

end
end Contingency.BitModel.StackCode

 

 

 

open Filter
namespace Contingency.BitModel.StackCode.IntegerDraw
open BinaryTrial
noncomputable section

theorem beValue_snoc (xs : List Bool) (b : Bool) :
    beValue (xs++[b])=2*beValue xs+b.toNat := by
  unfold beValue
  rw [List.foldl_append]
  rfl

theorem beValue_bits_reverse (N : ℕ) : beValue N.bits.reverse=N := by
  induction N using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit _ _ h,List.reverse_cons,beValue_snoc,ih]
    cases b <;> simp [Nat.bit]

theorem minimal_width (N : ℕ) : 2^N.size≤2*(N+1) := by
  by_cases hn : N.size=0
  · rw [hn]
    simp only [pow_zero]
    omega
  have hh := Nat.lt_size.mp (show N.size-1<N.size by omega)
  have he : N.size=(N.size-1)+1 := by omega
  calc
    2^N.size=2^(N.size-1)*2 := by conv_lhs => rw [he]; rw [pow_succ]
    _ ≤ N*2 := Nat.mul_le_mul_right 2 hh
    _ ≤ 2*(N+1) := by omega

def rawMaximum (N : ℕ) : List Bool := N.bits.reverse

@[simp] theorem rawMaximum_length (N : ℕ) : (rawMaximum N).length=N.size := by
  simp [rawMaximum,Nat.size_eq_bits_len]
@[simp] theorem rawMaximum_value (N : ℕ) : beValue (rawMaximum N)=N := beValue_bits_reverse N

def integerWord (N : ℕ) (u : Fin (N+1)) : List Bool :=
  validWord (rawMaximum N) ⟨u,by simpa using u.isLt⟩

@[simp] theorem integerWord_value (N : ℕ) (u : Fin (N+1)) : beValue (integerWord N u)=u.val := by
  unfold integerWord validWord
  rw [word_value]

@[simp] theorem integerWord_length (N : ℕ) (u : Fin (N+1)) : (integerWord N u).length=N.size := by
  simp [integerWord,validWord,word]

theorem machine_safe (B : List Bool) (t : ℕ) (f : Fin t→Bool) (hh : (machine.run B f).state=none) :
    ∃ u : Fin (beValue B+1),(machine.run B f).outputRev.reverse=validWord B u :=
  safe_compile program B (fun out => ∃ u : Fin (beValue B+1),out=validWord B u)
    (fun _ f hh => stack_safe B f hh) t f hh

 

theorem integer_sampler (N : ℕ) :
    (∀ (t : ℕ) (coins : Fin t→Bool),(machine.run (rawMaximum N) coins).state=none →
      ∃ u : Fin (N+1),(machine.run (rawMaximum N) coins).outputRev.reverse=integerWord N u) ∧
    Tendsto (machine.tail (rawMaximum N)) atTop (nhds 0) ∧
    (∀ u : Fin (N+1),Tendsto (machine.mass (rawMaximum N) (integerWord N u)) atTop (nhds (1/(N+1:ℝ)))) ∧
    Summable (machine.tail (rawMaximum N)) ∧
    (∑' t,machine.tail (rawMaximum N) t)≤52*(N.size:ℝ)+30 := by
  refine ⟨?_,machine_halts_ae _,?_,machine_summable _,?_⟩
  · intro t coins hh
    obtain ⟨u,hu⟩ := machine_safe (rawMaximum N) t coins hh
    refine ⟨⟨u,by simpa using u.isLt⟩,?_⟩
    exact hu
  · intro u
    simpa only [rawMaximum_value,integerWord] using machine_uniform (rawMaximum N) ⟨u,by simpa using u.isLt⟩
  · have hw : 2^(rawMaximum N).length≤2*(beValue (rawMaximum N)+1) := by
      simpa using minimal_width N
    simpa using machine_linear_expected (rawMaximum N) hw

end
end Contingency.BitModel.StackCode.IntegerDraw

 

 

 

namespace Contingency.BitModel.StackCode.BinarySubtract
noncomputable section

def outBit (a b carry : Bool) : Bool := xor (xor a b) carry
def nextBorrow (a b carry : Bool) : Bool := (!a && (b || carry)) || (b && carry)

theorem digit_identity (a b carry : Bool) :
    a.toNat+2*(nextBorrow a b carry).toNat = b.toNat+carry.toNat+(outBit a b carry).toNat := by
  cases a <;> cases b <;> cases carry <;> decide

def value : List Bool→ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs

structure Digit where
  a : Bool
  b : Bool

def output : List Digit → Bool → List Bool
  | [],_ => []
  | d::ds,c => outBit d.a d.b c :: output ds (nextBorrow d.a d.b c)

def borrow : List Digit → Bool → Bool
  | [],c => c
  | d::ds,c => borrow ds (nextBorrow d.a d.b c)

@[simp] theorem output_length (ds : List Digit) (c : Bool) : (output ds c).length=ds.length := by
  induction ds generalizing c with
  | nil => rfl
  | cons d ds ih => simp [output,ih]

theorem value_lt (bs : List Bool) : value bs<2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    change b.toNat+2*value bs<2^(bs.length+1)
    rw [pow_succ]
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem word_identity (ds : List Digit) (c : Bool) :
    value (ds.map Digit.a)+2^ds.length*(borrow ds c).toNat =
      value (ds.map Digit.b)+c.toNat+value (output ds c) := by
  induction ds generalizing c with
  | nil => simp [value,borrow,output]
  | cons d ds ih =>
    have hd := digit_identity d.a d.b c
    have hh := ih (nextBorrow d.a d.b c)
    simp only [List.map_cons,value,List.length_cons,pow_succ,borrow,output]
    nlinarith

theorem subtract_correct (ds : List Digit) (h : value (ds.map Digit.b)≤value (ds.map Digit.a)) :
    borrow ds false=false ∧ value (output ds false)=value (ds.map Digit.a)-value (ds.map Digit.b) := by
  have hh := word_identity ds false
  have ho := value_lt (output ds false)
  rw [output_length] at ho
  cases hb : borrow ds false <;> simp only [hb,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hh
  · exact ⟨rfl,by omega⟩
  · omega

inductive Q
  | start (carry : Bool)
  | second (carry a : Bool)
  | place (carry a b : Bool)
  | done (carry : Bool)
  deriving DecidableEq, Fintype

def label (q : Q) : Fin (Fintype.card Q) := Fintype.equivFin Q q

def code : Q→Op (Fintype.card Q) 4
  | .start c => .pop 0 (label (.done c)) (label (.second c false)) (label (.second c true))
  | .second c a => .pop 1 (label (.place c a false)) (label (.place c a false)) (label (.place c a true))
  | .place c a b => .push 2 (outBit a b c) (label (.start (nextBorrow a b c)))
  | .done _ => .halt

def program : Program := ⟨Fintype.card Q,4,label (.start false),fun pc => code ((Fintype.equivFin Q).symm pc)⟩
def config (q : Q) (m : Memory 4) : Config program := ⟨some (label q),m⟩

def digitMemory (d : Digit) (c : Bool) (m : Memory 4) : Memory 4 :=
  ((m.pop 0).pop 1).push 2 (outBit d.a d.b c)

def wordMemory : List Digit→Bool→Memory 4→Memory 4
  | [],_,m => m
  | d::ds,c,m => wordMemory ds (nextBorrow d.a d.b c) (digitMemory d c m)

theorem one_step (q : Q) (m : Memory 4) (coin : Bool) :
    step program coin (config q m)=
      ⟨(effect (code q) coin m).1,(effect (code q) coin m).2⟩ := by
  simp [step,config,program,label]

theorem first_step (m : Memory 4) (c a x : Bool) (as : List Bool) (ha : m.stack 0=a::as) :
    step program x (config (.start c) m)=config (.second c a) (m.pop 0) := by
  rw [one_step]
  cases a <;> simp [code,effect,branch,ha,config] <;> rfl

theorem second_step (m : Memory 4) (c a b x : Bool) (bs : List Bool) (hb : m.stack 1=b::bs) :
    step program x (config (.second c a) m)=config (.place c a b) (m.pop 1) := by
  rw [one_step]
  cases b <;> simp [code,effect,branch,hb,config] <;> rfl

theorem third_step (m : Memory 4) (c a b x : Bool) :
    step program x (config (.place c a b) m)=
      config (.start (nextBorrow a b c)) (m.push 2 (outBit a b c)) := by
  rw [one_step]
  rfl

theorem three_steps (m : Memory 4) (d : Digit) (c x y z : Bool) (as bs : List Bool)
    (ha : m.stack 0=d.a::as) (hb : m.stack 1=d.b::bs) :
    [x,y,z].foldl (fun cfg b => step program b cfg) (config (.start c) m)=
      config (.start (nextBorrow d.a d.b c)) (digitMemory d c m) := by
  simp only [List.foldl_cons,List.foldl_nil]
  rw [first_step m c d.a x as ha,second_step _ c d.a d.b y bs,third_step]
  · rfl
  · simpa using hb

theorem pass (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b) :
    (List.replicate (3*ds.length) false).foldl (fun cfg b => step program b cfg) (config (.start c) m)=
      config (.start (borrow ds c)) (wordMemory ds c m) := by
  induction ds generalizing c m with
  | nil => rfl
  | cons d ds ih =>
    have he : 3*(d::ds).length=3+3*ds.length := by simp; omega
    rw [he,List.replicate_add,List.foldl_append]
    change (List.replicate (3*ds.length) false).foldl _
      ([false,false,false].foldl _ (config (.start c) m))=_
    rw [three_steps m d c false false false _ _ ha hb,ih]
    · rfl
    · simp [digitMemory,Memory.push,Memory.pop,ha]
    · simp [digitMemory,Memory.push,Memory.pop,hb]

end
end Contingency.BitModel.StackCode.BinarySubtract

 

 

 

namespace Contingency.BitModel.StackCode.BinarySubtract
noncomputable section

theorem step_independent (cfg : Config program) (b b' : Bool) : step program b cfg=step program b' cfg := by
  rcases cfg with ⟨s,m⟩
  cases s with
  | none => rfl
  | some pc =>
    unfold step
    dsimp only [program]
    cases (Fintype.equivFin Q).symm pc <;> rfl

theorem fold_independent (xs ys : List Bool) (hl : xs.length=ys.length) (cfg : Config program) :
    xs.foldl (fun cfg b => step program b cfg) cfg=ys.foldl (fun cfg b => step program b cfg) cfg := by
  induction xs generalizing ys cfg with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hl
      simp only [List.foldl_cons]
      rw [step_independent _ x y]
      exact ih _ hl _

theorem pass_any (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b)
    (coins : List Bool) (hl : coins.length=3*ds.length) :
    coins.foldl (fun cfg b => step program b cfg) (config (.start c) m)=
      config (.start (borrow ds c)) (wordMemory ds c m) := by
  rw [fold_independent coins (List.replicate (3*ds.length) false) (by simpa using hl)]
  exact pass ds c m ha hb

theorem wordMemory_stacks (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b) :
    (wordMemory ds c m).stack 0=[] ∧ (wordMemory ds c m).stack 1=[] ∧
    (wordMemory ds c m).stack 2=(output ds c).reverse++m.stack 2 ∧
    (wordMemory ds c m).stack 3=m.stack 3 ∧
    (wordMemory ds c m).input=m.input ∧ (wordMemory ds c m).outputRev=m.outputRev := by
  induction ds generalizing c m with
  | nil => exact ⟨ha,hb,rfl,rfl,rfl,rfl⟩
  | cons d ds ih =>
    have h0 : (digitMemory d c m).stack 0=ds.map Digit.a := by
      simp [digitMemory,Memory.push,Memory.pop,ha]
    have h1 : (digitMemory d c m).stack 1=ds.map Digit.b := by
      simp [digitMemory,Memory.push,Memory.pop,hb]
    have hh := ih (nextBorrow d.a d.b c) (digitMemory d c m) h0 h1
    refine ⟨hh.1,hh.2.1,?_,?_,hh.2.2.2.2.1,hh.2.2.2.2.2⟩
    · simpa [wordMemory,output,List.reverse_cons,List.append_assoc,digitMemory,Memory.push,Memory.pop,Function.update_apply] using hh.2.2.1
    · simpa [wordMemory,digitMemory,Memory.push,Memory.pop,Function.update_apply] using hh.2.2.2.1

theorem finish (m : Memory 4) (c b : Bool) (hm : m.stack 0=[]) :
    step program b (config (.start c) m)=config (.done c) (m.pop 0) := by
  simp [step,program,config,label,code,effect,branch,hm]

theorem halt (m : Memory 4) (c b : Bool) :
    step program b (config (.done c) m)=⟨none,m⟩ := by
  simp [step,program,config,label,code,effect]

theorem finish_run (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b)
    (coins : List Bool) (hl : coins.length=3*ds.length) (b b' : Bool) :
    (coins++[b,b']).foldl (fun cfg b => step program b cfg) (config (.start c) m)=
      ⟨none,(wordMemory ds c m).pop 0⟩ := by
  rw [List.foldl_append,pass_any ds c m ha hb coins hl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [finish _ _ _ (wordMemory_stacks ds c m ha hb).1,halt]

theorem fold_compiled (P : Program) (cfg : Config P) {t : ℕ} (coins : Fin (t*2)→Bool) :
    (List.ofFn coins).foldl (fun cfg b => (compile P).step b cfg) (encode P cfg)=
      encode P ((List.ofFn (fun i : Fin t => coins (second i))).foldl (fun cfg b => step P b cfg) cfg) := by
  rw [coins_as_pairs,fold_pairs]
  congr 1
  have hh := List.foldl_map (f:=Prod.snd) (g:=fun cfg b => step P b cfg)
    (l:=List.ofFn fun i : Fin t => (coins (first i),coins (second i))) (init:=cfg)
  simpa only [List.map_ofFn,Function.comp_def] using hh.symm

 

theorem tape_pass (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b)
    (coins : Fin ((3*ds.length)*2)→Bool) :
    (List.ofFn coins).foldl (fun cfg b => (compile program).step b cfg) (encode program (config (.start c) m))=
      encode program (config (.start (borrow ds c)) (wordMemory ds c m)) := by
  rw [fold_compiled,pass_any ds c m ha hb _ (by simp)]

end
end Contingency.BitModel.StackCode.BinarySubtract

 

 

 

namespace Contingency.BitModel.StackCode.BinaryAdd
open BinarySubtract
noncomputable section

def nextCarry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

theorem digit_identity (a b c : Bool) :
    a.toNat+b.toNat+c.toNat = (outBit a b c).toNat+2*(nextCarry a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

def output : List Digit → Bool → List Bool
  | [],_ => []
  | d::ds,c => outBit d.a d.b c :: output ds (nextCarry d.a d.b c)

def carry : List Digit → Bool → Bool
  | [],c => c
  | d::ds,c => carry ds (nextCarry d.a d.b c)

@[simp] theorem output_length (ds : List Digit) (c : Bool) : (output ds c).length=ds.length := by
  induction ds generalizing c with
  | nil => rfl
  | cons d ds ih => simp [output,ih]

theorem word_identity (ds : List Digit) (c : Bool) :
    value (ds.map Digit.a)+value (ds.map Digit.b)+c.toNat =
      value (output ds c)+2^ds.length*(carry ds c).toNat := by
  induction ds generalizing c with
  | nil => simp [value,carry,output]
  | cons d ds ih =>
    have hd := digit_identity d.a d.b c
    have hh := ih (nextCarry d.a d.b c)
    simp only [List.map_cons,value,List.length_cons,pow_succ,carry,output]
    nlinarith

inductive Q
  | start (carry : Bool)
  | second (carry a : Bool)
  | place (carry a b : Bool)
  | done (carry : Bool)
  | halt
  deriving DecidableEq, Fintype

def label (q : Q) : Fin (Fintype.card Q) := Fintype.equivFin Q q

def code : Q→Op (Fintype.card Q) 4
  | .start c => .pop 0 (label (.done c)) (label (.second c false)) (label (.second c true))
  | .second c a => .pop 1 (label (.place c a false)) (label (.place c a false)) (label (.place c a true))
  | .place c a b => .push 2 (outBit a b c) (label (.start (nextCarry a b c)))
  | .done c => .push 2 c (label .halt)
  | .halt => .halt

def program : Program := ⟨Fintype.card Q,4,label (.start false),fun pc => code ((Fintype.equivFin Q).symm pc)⟩
def config (q : Q) (m : Memory 4) : Config program := ⟨some (label q),m⟩

def digitMemory (d : Digit) (c : Bool) (m : Memory 4) : Memory 4 :=
  ((m.pop 0).pop 1).push 2 (outBit d.a d.b c)

def wordMemory : List Digit→Bool→Memory 4→Memory 4
  | [],_,m => m
  | d::ds,c,m => wordMemory ds (nextCarry d.a d.b c) (digitMemory d c m)

theorem one_step (q : Q) (m : Memory 4) (coin : Bool) :
    step program coin (config q m)=
      ⟨(effect (code q) coin m).1,(effect (code q) coin m).2⟩ := by
  simp [step,config,program,label]

theorem first_step (m : Memory 4) (c a x : Bool) (as : List Bool) (ha : m.stack 0=a::as) :
    step program x (config (.start c) m)=config (.second c a) (m.pop 0) := by
  rw [one_step]
  cases a <;> simp [code,effect,branch,ha,config] <;> rfl

theorem second_step (m : Memory 4) (c a b x : Bool) (bs : List Bool) (hb : m.stack 1=b::bs) :
    step program x (config (.second c a) m)=config (.place c a b) (m.pop 1) := by
  rw [one_step]
  cases b <;> simp [code,effect,branch,hb,config] <;> rfl

theorem third_step (m : Memory 4) (c a b x : Bool) :
    step program x (config (.place c a b) m)=
      config (.start (nextCarry a b c)) (m.push 2 (outBit a b c)) := by
  rw [one_step]
  rfl

theorem three_steps (m : Memory 4) (d : Digit) (c x y z : Bool) (as bs : List Bool)
    (ha : m.stack 0=d.a::as) (hb : m.stack 1=d.b::bs) :
    [x,y,z].foldl (fun cfg b => step program b cfg) (config (.start c) m)=
      config (.start (nextCarry d.a d.b c)) (digitMemory d c m) := by
  simp only [List.foldl_cons,List.foldl_nil]
  rw [first_step m c d.a x as ha,second_step _ c d.a d.b y bs,third_step]
  · rfl
  · simpa using hb

theorem pass (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b) :
    (List.replicate (3*ds.length) false).foldl (fun cfg b => step program b cfg) (config (.start c) m)=
      config (.start (carry ds c)) (wordMemory ds c m) := by
  induction ds generalizing c m with
  | nil => rfl
  | cons d ds ih =>
    have he : 3*(d::ds).length=3+3*ds.length := by simp; omega
    rw [he,List.replicate_add,List.foldl_append]
    change (List.replicate (3*ds.length) false).foldl _
      ([false,false,false].foldl _ (config (.start c) m))=_
    rw [three_steps m d c false false false _ _ ha hb,ih]
    · rfl
    · simp [digitMemory,Memory.push,Memory.pop,ha]
    · simp [digitMemory,Memory.push,Memory.pop,hb]

end
end Contingency.BitModel.StackCode.BinaryAdd

 

 

 

namespace Contingency.BitModel.StackCode.BinaryAdd
open BinarySubtract
noncomputable section

theorem step_independent (cfg : Config program) (b b' : Bool) : step program b cfg=step program b' cfg := by
  rcases cfg with ⟨s,m⟩
  cases s with
  | none => rfl
  | some pc =>
    unfold step
    dsimp only [program]
    cases (Fintype.equivFin Q).symm pc <;> rfl

theorem fold_independent (xs ys : List Bool) (hl : xs.length=ys.length) (cfg : Config program) :
    xs.foldl (fun cfg b => step program b cfg) cfg=ys.foldl (fun cfg b => step program b cfg) cfg := by
  induction xs generalizing ys cfg with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hl
      simp only [List.foldl_cons]
      rw [step_independent _ x y]
      exact ih _ hl _

theorem pass_any (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b)
    (coins : List Bool) (hl : coins.length=3*ds.length) :
    coins.foldl (fun cfg b => step program b cfg) (config (.start c) m)=
      config (.start (carry ds c)) (wordMemory ds c m) := by
  rw [fold_independent coins (List.replicate (3*ds.length) false) (by simpa using hl)]
  exact pass ds c m ha hb

theorem wordMemory_stacks (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b) :
    (wordMemory ds c m).stack 0=[] ∧ (wordMemory ds c m).stack 1=[] ∧
    (wordMemory ds c m).stack 2=(output ds c).reverse++m.stack 2 ∧
    (wordMemory ds c m).stack 3=m.stack 3 ∧
    (wordMemory ds c m).input=m.input ∧ (wordMemory ds c m).outputRev=m.outputRev := by
  induction ds generalizing c m with
  | nil => exact ⟨ha,hb,rfl,rfl,rfl,rfl⟩
  | cons d ds ih =>
    have h0 : (digitMemory d c m).stack 0=ds.map Digit.a := by
      simp [digitMemory,Memory.push,Memory.pop,ha]
    have h1 : (digitMemory d c m).stack 1=ds.map Digit.b := by
      simp [digitMemory,Memory.push,Memory.pop,hb]
    have hh := ih (nextCarry d.a d.b c) (digitMemory d c m) h0 h1
    refine ⟨hh.1,hh.2.1,?_,?_,hh.2.2.2.2.1,hh.2.2.2.2.2⟩
    · simpa [wordMemory,output,List.reverse_cons,List.append_assoc,digitMemory,Memory.push,Memory.pop,Function.update_apply] using hh.2.2.1
    · simpa [wordMemory,digitMemory,Memory.push,Memory.pop,Function.update_apply] using hh.2.2.2.1

theorem finish (m : Memory 4) (c b : Bool) (hm : m.stack 0=[]) :
    step program b (config (.start c) m)=config (.done c) (m.pop 0) := by
  simp [step,program,config,label,code,effect,branch,hm]

theorem final_carry (m : Memory 4) (c b : Bool) :
    step program b (config (.done c) m)=config .halt (m.push 2 c) := by
  rw [one_step]; rfl

theorem halt (m : Memory 4) (b : Bool) :
    step program b (config .halt m)=⟨none,m⟩ := by
  rw [one_step]; rfl

theorem finish_run (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b)
    (coins : List Bool) (hl : coins.length=3*ds.length) (b b' b'' : Bool) :
    (coins++[b,b',b'']).foldl (fun cfg b => step program b cfg) (config (.start c) m)=
      ⟨none,((wordMemory ds c m).pop 0).push 2 (carry ds c)⟩ := by
  rw [List.foldl_append,pass_any ds c m ha hb coins hl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [finish _ _ _ (wordMemory_stacks ds c m ha hb).1,final_carry,halt]

 

theorem tape_pass (ds : List Digit) (c : Bool) (m : Memory 4)
    (ha : m.stack 0=ds.map Digit.a) (hb : m.stack 1=ds.map Digit.b)
    (coins : Fin ((3*ds.length)*2)→Bool) :
    (List.ofFn coins).foldl (fun cfg b => (compile program).step b cfg) (encode program (config (.start c) m))=
      encode program (config (.start (carry ds c)) (wordMemory ds c m)) := by
  rw [BinarySubtract.fold_compiled,pass_any ds c m ha hb _ (by simp)]

end
end Contingency.BitModel.StackCode.BinaryAdd

 

 

 

namespace Contingency.BitModel.StackCode.BinarySubtract
noncomputable section

theorem value_append_false (xs : List Bool) (n : ℕ) :
    value (xs++List.replicate n false)=value xs := by
  induction xs with
  | nil =>
    simp only [List.nil_append,value]
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ,value,ih]
  | cons b xs ih => simp [value,ih]

theorem value_bits (x : ℕ) : value x.bits=x := by
  induction x using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit _ _ h]
    change b.toNat+2*value n.bits=Nat.bit b n
    rw [ih]
    cases b <;> simp [Nat.bit]
    omega

def bits (n x : ℕ) : List Bool := x.bits++List.replicate (n-x.size) false

@[simp] theorem bits_length (n x : ℕ) (h : x<2^n) : (bits n x).length=n := by
  have hh := Nat.size_le.mpr h
  simp only [bits,List.length_append,List.length_replicate]
  have he := Nat.size_eq_bits_len x
  omega

@[simp] theorem bits_value (n x : ℕ) : value (bits n x)=x := by
  rw [bits,value_append_false,value_bits]

def digits (as bs : List Bool) : List Digit := List.zipWith Digit.mk as bs

theorem digits_maps (as bs : List Bool) (h : as.length=bs.length) :
    (digits as bs).map Digit.a=as ∧ (digits as bs).map Digit.b=bs ∧
    (digits as bs).length=as.length := by
  induction as generalizing bs with
  | nil =>
    have he : bs=[] := List.length_eq_zero_iff.mp (by simpa using h.symm)
    subst bs
    exact ⟨rfl,rfl,rfl⟩
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have hh := ih bs (by simpa using h)
      simpa [digits,List.zipWith_cons_cons] using hh

theorem borrow_iff (ds : List Digit) :
    borrow ds false=true ↔ value (ds.map Digit.a)<value (ds.map Digit.b) := by
  have hi := word_identity ds false
  have ha := value_lt (ds.map Digit.a)
  have hd := value_lt (output ds false)
  simp only [List.length_map,output_length] at ha hd
  cases hb : borrow ds false <;>
    simp only [hb,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hi
  · constructor
    · intro h; cases h
    · intro h; omega
  · constructor
    · intro h; omega
    · intro h; rfl

 

theorem padded_subtraction (n x y : ℕ) (hx : x<2^n) (hy : y<2^n) :
    let ds := digits (bits n x) (bits n y)
    ds.length=n ∧ (borrow ds false=true ↔ x<y) ∧
      (y≤x → value (output ds false)=x-y) := by
  dsimp only
  obtain ⟨ha,hb,hl⟩ := digits_maps (bits n x) (bits n y) (by rw [bits_length _ _ hx,bits_length _ _ hy])
  refine ⟨hl.trans (bits_length _ _ hx),?_,?_⟩
  · simpa [ha,hb] using borrow_iff (digits (bits n x) (bits n y))
  · intro h
    have hh := subtract_correct (digits (bits n x) (bits n y)) (by simpa [ha,hb] using h)
    simpa [ha,hb] using hh.2

end
end Contingency.BitModel.StackCode.BinarySubtract

end

end OAI

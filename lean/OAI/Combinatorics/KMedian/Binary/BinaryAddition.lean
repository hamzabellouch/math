import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanFinite
import OAI.Combinatorics.KMedian.Binary.BooleanRecode
import OAI.Combinatorics.KMedian.Binary.BinaryWords

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def sumBit (a b c : Bool) : Bool := xor (xor a b) c
 def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

 theorem fullAdder (a b c : Bool) :
    (sumBit a b c).toNat+2*(carryBit a b c).toNat=a.toNat+b.toNat+c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

 def add : List Bool → List Bool → Bool → List Bool
  | [],[],c => if c then [true] else []
  | a::xs,ys,c => sumBit a (ys.head?.getD false) c :: add xs ys.tail (carryBit a (ys.head?.getD false) c)
  | [],b::ys,c => sumBit false b c :: add [] ys (carryBit false b c)
termination_by xs ys _ => xs.length+ys.length

 theorem add_step (xs ys : List Bool) (c : Bool) (h : (xs.isEmpty && ys.isEmpty)=false) :
    add xs ys c=sumBit (xs.head?.getD false) (ys.head?.getD false) c ::
      add xs.tail ys.tail (carryBit (xs.head?.getD false) (ys.head?.getD false) c) := by
  cases xs <;> cases ys <;> simp_all only [List.isEmpty_nil,List.isEmpty_cons,Bool.true_and,Bool.false_and,
    Bool.true_eq_false,List.head?_cons,List.head?_nil,Option.getD_some,Option.getD_none,
    List.tail_nil,List.tail_cons,add]

 theorem value_add (xs ys : List Bool) (c : Bool) : value (add xs ys c)=value xs+value ys+c.toNat := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [add,value]
      | cons b ys ih =>
          rw [add,value_cons,ih]
          have h := fullAdder false b c
          simp only [value_nil,value_cons,Bool.toNat_false] at *
          omega
  | cons a xs ih =>
      rw [add,value_cons,ih]
      have h := fullAdder a (ys.head?.getD false) c
      cases ys with
      | nil => simp only [List.head?_nil,Option.getD_none,List.tail_nil,value_nil,value_cons,Bool.toNat_false] at *; omega
      | cons b ys => simp only [List.head?_cons,Option.getD_some,List.tail_cons,value_cons] at *; omega

end Word

namespace AdditionLoop
abbrev S := List Bool × (List Bool × (Bool × List Bool))
abbrev ec : Bool × List Bool → List Bool := encodePair encodeBool id
abbrev ey : List Bool × (Bool × List Bool) → List Bool := encodePair id ec
abbrev enc : S → List Bool := encodePair id ey
 def empty (s : S) : Bool := s.1.isEmpty && s.2.1.isEmpty
 def next (s : S) : S :=
  (s.1.tail,(s.2.1.tail,(Word.carryBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1,
    Word.sumBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1 :: s.2.2.2)))
 def finish (s : S) : List Bool := (if s.2.2.1 then true::s.2.2.2 else s.2.2.2).reverse
 def body (s : S) : List Bool ⊕ S := if empty s then .inl (finish s) else .inr (next s)
 def result (s : S) : List Bool := s.2.2.2.reverse++Word.add s.1 s.2.1 s.2.2.1

 theorem enc_length (s : S) : (enc s).length=2*s.1.length+2*s.2.1.length+s.2.2.2.length+5 := by
  simp only [enc,ey,ec,encodePair_length,encodeBool,id_eq,List.length_cons,List.length_nil]
  omega

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let px := PolyProgram.fst id ey
  let pyz := PolyProgram.snd id ey
  let py := pyz.comp (PolyProgram.fst id ec)
  let pca := pyz.comp (PolyProgram.snd id ec)
  let pc := pca.comp (PolyProgram.fst encodeBool id)
  let pa := pca.comp (PolyProgram.snd encodeBool id)
  let bits := (px.comp PolyProgram.head).fanout ((py.comp PolyProgram.head).fanout pc)
  let binj := encodePair_injective encodeBool_injective (encodePair_injective encodeBool_injective encodeBool_injective)
  let sb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.sumBit v.1 v.2.1 v.2.2) binj)
  let cb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.carryBit v.1 v.2.1 v.2.2) binj)
  let na := (sb.fanout pa).comp PolyProgram.cons
  let pn := (px.comp PolyProgram.tail).fanout ((py.comp PolyProgram.tail).fanout (cb.fanout na))
  let pe := ((px.comp PolyProgram.isEmpty).fanout (py.comp PolyProgram.isEmpty)).comp PolyProgram.boolAnd
  let pf := (PolyProgram.ite pc pa ((PolyProgram.constant enc encodeBool true).fanout pa |>.comp PolyProgram.cons)).comp PolyProgram.reverse
  exact (PolyProgram.ite pe (pn.comp (PolyProgram.injectRight enc id))
    (pf.comp (PolyProgram.injectLeft enc id))).congr _ (fun _ => rfl)

 theorem shorten (s : S) (h : empty s=false) :
    s.1.tail.length+s.2.1.tail.length<s.1.length+s.2.1.length := by
  rcases s with ⟨xs,ys,c,acc⟩
  cases xs <;> cases ys <;> simp_all [empty]
  omega

 theorem next_result (s : S) (h : empty s=false) : result (next s)=result s := by
  simp only [result]
  rw [Word.add_step s.1 s.2.1 s.2.2.1 h]
  simp only [next,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem next_size (s : S) (h : empty s=false) : (enc (next s)).length≤(enc s).length := by
  have hs := shorten s h
  simp only [enc_length,next,List.length_cons]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.length+s.2.1.length=L → (enc s).length≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      cases he : empty s with
      | true =>
          refine ⟨1,by omega,BoundedRun.stop hs ?_⟩
          rcases s with ⟨xs,ys,c,acc⟩
          have hz : xs=[] ∧ ys=[] := by simpa only [empty,Bool.and_eq_true,List.isEmpty_iff] using he
          rcases hz with ⟨rfl,rfl⟩
          cases c <;> simp [body,empty,finish,result,Word.add]
      | false =>
          have hl : (next s).1.length+(next s).2.1.length<L := by simpa only [next,hL] using shorten s he
          obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl ((next_size s he).trans hs)
          refine ⟨n+1,by omega,?_⟩
          rw [next_result s he] at hr
          exact BoundedRun.step hs (by simp only [body,he,Bool.false_eq_true,ite_false]) hr

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    obtain ⟨n,hn,hr⟩ := run (s.1.length+s.2.1.length) s (enc s).length rfl le_rfl
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_X] using hr)

end AdditionLoop

namespace PolyProgram
noncomputable def addWords : PolyProgram (encodePair id id) id (fun x : List Bool × List Bool => Word.add x.1 x.2 false) := by
  let ex : List Bool × List Bool → List Bool := encodePair id id
  let init := (fst id id).fanout ((snd id id).fanout (constant ex AdditionLoop.ec (false,[])))
  exact (init.comp AdditionLoop.loop).congr _ (fun _ => rfl)

noncomputable def natAdd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1+x.2) :=
  (addWords.comp toBits).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_add,Word.value_bits,Bool.toNat_false,Nat.add_zero])
end PolyProgram
end MetricKMedian.Binary
end

end OAI

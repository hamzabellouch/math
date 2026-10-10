import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryNatural
import OAI.Combinatorics.KMedian.Binary.BinarySubtraction

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace DivisionLoop
 def qstep (b : Bool) (d q r : ℕ) : ℕ := Nat.bit (!decide (Nat.bit b r<d)) q
 def rstep (b : Bool) (d r : ℕ) : ℕ := if Nat.bit b r<d then Nat.bit b r else Nat.bit b r-d

 theorem step_total (b : Bool) (d q r : ℕ) :
    qstep b d q r*d+rstep b d r=2*(q*d+r)+b.toNat := by
  by_cases ht : Nat.bit b r<d
  · rw [qstep,rstep,ite_eq_left ht,decide_eq_true ht]
    simp only [Bool.not_true,Nat.bit_val,Bool.toNat_false]
    ring
  · have hd : d≤Nat.bit b r := by omega
    have he := Nat.sub_add_cancel hd
    rw [qstep,rstep,ite_eq_right ht,decide_eq_false ht]
    simp only [Bool.not_false,Nat.bit_val,Bool.toNat_true] at *
    nlinarith

 theorem step_remainder (b : Bool) (d r : ℕ) (_ : 0<d) (hr : r<d) : rstep b d r<d := by
  have hb : b.toNat≤1 := by cases b <;> decide
  unfold rstep
  split_ifs with ht
  · exact ht
  · simp only [Nat.bit_val] at *
    omega

 def eval : List Bool → ℕ → ℕ → ℕ → ℕ × ℕ
  | [],_,q,r => (q,r)
  | b::xs,d,q,r => eval xs d (qstep b d q r) (rstep b d r)

 theorem eval_spec (xs : List Bool) (d q r : ℕ) (hd : 0<d) (hr : r<d) :
    (eval xs d q r).2<d ∧
      (eval xs d q r).1*d+(eval xs d q r).2=2^xs.length*(q*d+r)+Word.value xs.reverse := by
  induction xs generalizing q r with
  | nil => exact ⟨hr,by simp [eval]⟩
  | cons b xs ih =>
      obtain ⟨hrem,heq⟩ := ih (qstep b d q r) (rstep b d r) (step_remainder b d r hd hr)
      refine ⟨hrem,?_⟩
      change (eval xs d (qstep b d q r) (rstep b d r)).1*d+
        (eval xs d (qstep b d q r) (rstep b d r)).2=_
      rw [heq,step_total]
      simp only [List.length_cons,List.reverse_cons,Word.value_append,Word.value_cons,Word.value_nil,
        Nat.mul_zero,Nat.add_zero,List.length_reverse,pow_succ]
      ring

abbrev S := List Bool × (ℕ × (ℕ × ℕ))
abbrev eqr : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
abbrev edqr : ℕ × (ℕ × ℕ) → List Bool := encodePair Nat.bits eqr
abbrev enc : S → List Bool := encodePair id edqr
 def next (s : S) : S :=
  (s.1.tail,(s.2.1,(qstep (s.1.head?.getD false) s.2.1 s.2.2.1 s.2.2.2,
    rstep (s.1.head?.getD false) s.2.1 s.2.2.2)))
 def body (s : S) : (ℕ × ℕ) ⊕ S := if s.1.isEmpty then .inl s.2.2 else .inr (next s)
 def result (s : S) : ℕ × ℕ := eval s.1 s.2.1 s.2.2.1 s.2.2.2
 def potential (s : S) : ℕ := s.1.length+max s.2.2.1.bits.length s.2.2.2.bits.length

 theorem enc_length (s : S) :
    (enc s).length=2*s.1.length+2*s.2.1.bits.length+2*s.2.2.1.bits.length+s.2.2.2.bits.length+3 := by
  simp only [enc,edqr,eqr,encodePair_length,id_eq]
  omega

 theorem total_le_length (s : S) : potential s+s.2.1.bits.length≤(enc s).length := by
  simp only [potential,enc_length]
  omega

 theorem length_le_total (s : S) : (enc s).length≤3*(potential s+s.2.1.bits.length)+3 := by
  simp only [potential,enc_length]
  omega

 theorem next_potential (s : S) (h : s.1.isEmpty=false) : potential (next s)≤potential s := by
  have hx : s.1.tail.length<s.1.length := by
    cases hh : s.1 with
    | nil => simp only [hh,List.isEmpty_nil] at h; contradiction
    | cons b xs => simp only [List.tail_cons,List.length_cons]; omega
  have hq := NatBinary.bit_length (!decide (Nat.bit (s.1.head?.getD false) s.2.2.2<s.2.1)) s.2.2.1
  have hr := NatBinary.bit_length (s.1.head?.getD false) s.2.2.2
  have hrle : rstep (s.1.head?.getD false) s.2.1 s.2.2.2≤Nat.bit (s.1.head?.getD false) s.2.2.2 := by
    unfold rstep
    split_ifs <;> omega
  have hrl := (NatBinary.length_mono hrle).trans hr
  simp only [potential,next,qstep]
  omega

 theorem next_result (s : S) (h : s.1.isEmpty=false) : result (next s)=result s := by
  rcases s with ⟨xs,d,q,r⟩
  cases xs with
  | nil => contradiction
  | cons b xs => rfl

noncomputable def program : PolyProgram enc (encodeLoop enc eqr) body := by
  let px := PolyProgram.fst id edqr
  let pdqr := PolyProgram.snd id edqr
  let pd := pdqr.comp (PolyProgram.fst Nat.bits eqr)
  let pqr := pdqr.comp (PolyProgram.snd Nat.bits eqr)
  let pq := pqr.comp (PolyProgram.fst Nat.bits Nat.bits)
  let pr := pqr.comp (PolyProgram.snd Nat.bits Nat.bits)
  let pb := px.comp PolyProgram.head
  let pt := (pb.fanout pr).comp PolyProgram.natBit
  let plt := (pt.fanout pd).comp PolyProgram.natLT
  let nq := ((plt.comp PolyProgram.boolNot).fanout pq).comp PolyProgram.natBit
  let nr := PolyProgram.ite plt ((pt.fanout pd).comp PolyProgram.natSub) pt
  let pn := (px.comp PolyProgram.tail).fanout (pd.fanout (nq.fanout nr))
  exact (PolyProgram.ite (px.comp PolyProgram.isEmpty)
    (pn.comp (PolyProgram.injectRight enc eqr))
    (pqr.comp (PolyProgram.injectLeft enc eqr))).congr _ (fun s => by
      simp only [Function.comp_apply,body,next,qstep,rstep,decide_eq_true_eq])

 theorem run (xs : List Bool) (d q r S : ℕ) (hs : 3*(potential (xs,d,q,r)+d.bits.length)+3≤S) :
    BoundedRun enc body S (xs.length+1) (xs,d,q,r) (result (xs,d,q,r)) := by
  induction xs generalizing q r with
  | nil =>
      exact BoundedRun.stop ((length_le_total ([],d,q,r)).trans hs) rfl
  | cons b xs ih =>
      let s : DivisionLoop.S := (b::xs,d,q,r)
      have hp := next_potential s rfl
      change 3*(potential s+d.bits.length)+3≤S at hs
      have hnext : 3*(potential (next s)+d.bits.length)+3≤S := by omega
      have hr := ih (qstep b d q r) (rstep b d r) hnext
      have hh : result (xs,d,qstep b d q r,rstep b d r)=result s := rfl
      rw [hh] at hr
      exact BoundedRun.step ((length_le_total s).trans hs) rfl hr

noncomputable def loop : PolyProgram enc eqr result :=
  program.loop result (X+1) (3*X+3) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [Polynomial.eval_add,eval_X,eval_one,enc_length]; omega
    · have hs := total_le_length s
      simpa only [Polynomial.eval_add,eval_mul,eval_ofNat,eval_X] using
        run s.1 s.2.1 s.2.2.1 s.2.2.2 (3*(enc s).length+3) (by
          change 3*(potential s+s.2.1.bits.length)+3≤3*(enc s).length+3
          omega))
end DivisionLoop

namespace PolyProgram
noncomputable def natDivMod : PolyProgram (encodePair Nat.bits Nat.bits) (encodePair Nat.bits Nat.bits)
    (fun x : ℕ × ℕ => (x.1/x.2,x.1%x.2)) := by
  let ex : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
  let px := fst Nat.bits Nat.bits
  let pd := snd Nat.bits Nat.bits
  let rev : PolyProgram Nat.bits id (fun n => n.bits.reverse) := reverse.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
  let init := (px.comp rev).fanout (pd.fanout (constant ex DivisionLoop.eqr (0,0)))
  let normal := init.comp DivisionLoop.loop
  let zeroCase := (constant ex Nat.bits 0).fanout px
  refine (ite (pd.comp natZero) normal zeroCase).congr _ ?_
  intro x
  change (if decide (x.2=0) then (0,x.1) else DivisionLoop.eval x.1.bits.reverse x.2 0 0)=_
  by_cases hd : x.2=0
  · simp only [hd,decide_true,ite_true,Nat.div_zero,Nat.mod_zero]
  · simp only [decide_eq_false hd,Bool.false_eq_true,ite_false]
    obtain ⟨hr,he⟩ := DivisionLoop.eval_spec x.1.bits.reverse x.2 0 0 (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero hd)
    simp only [zero_mul,zero_add,mul_zero,zero_add,List.reverse_reverse,Word.value_bits] at he
    have hp : x.1/x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).1 ∧
        x.1%x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).2 :=
      (Nat.div_mod_unique (Nat.pos_of_ne_zero hd)).mpr ⟨by
        simpa only [Nat.mul_comm,Nat.add_comm] using he,hr⟩
    exact Prod.ext hp.1.symm hp.2.symm

noncomputable def natDiv : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1/x.2) :=
  (natDivMod.comp (fst Nat.bits Nat.bits)).congr _ (fun _ => rfl)
noncomputable def natMod : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1%x.2) :=
  (natDivMod.comp (snd Nat.bits Nat.bits)).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI

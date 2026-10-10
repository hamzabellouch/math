import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.GuardMachineBase

namespace OAI

namespace MatchingFPRAS.BinaryArithmetic
open Turing MachineCost

def incrementBits : List Bool → List Bool
  | [] => [true]
  | false::bs => true::bs
  | true::bs => false::incrementBits bs
lemma incrementBits_bits (n : ℕ) : incrementBits n.bits=(n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [incrementBits]
  | bit b n h ih =>
    cases b with
    | false =>
      have hn : n≠0 := by intro hh; have := h hh; contradiction
      simp only [Nat.bit, Bool.cond_false, Nat.bit0_bits _ hn, incrementBits]
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [Nat.bits_append_bit _ _ h,incrementBits,ih]
      have hn : n+1≠0 := by omega
      have he : Nat.bit true n+1=2*(n+1) := by simp [Nat.bit]; omega
      rw [he,Nat.bit0_bits _ hn]

def numeral (bs : List Bool) : List Symbol := (bs.map fun b=>if b then 2 else 1)++[3]

def incrementProgram : Bool → TM1.Stmt Symbol Bool Unit
  | false => .branch (fun a _=>a==1)
      (.write (fun _ _=>2) (.goto (fun _ _=>true)))
      (.branch (fun a _=>a==2)
        (.write (fun _ _=>1) (.move .right (.goto (fun _ _=>false))))
        (.write (fun _ _=>2) (.move .right (.write (fun _ _=>3) (.move .left (.goto (fun _ _=>true)))))))
  | true => .branch (fun a _=>a==0) (.move .right .halt) (.move .left (.goto (fun _ _=>true)))
abbrev cfg (s : Option Bool) (L R : List Symbol) : TM1.Cfg Symbol Bool Unit :=
  ⟨s,(),Tape.mk₂ L R⟩
lemma back_step (L R : List Symbol) (a : Symbol) (ha : a≠0) :
    advance (TM1.step incrementProgram) (cfg (some true) L (a::R))=
      ⟨some true,(),(Tape.mk₂ L (a::R)).move .left⟩ := by
  have ha' : (a==0)=false := by simpa using ha
  simp [advance,TM1.step,incrementProgram,TM1.stepAux,cfg,Tape.mk₂,Tape.mk',ha']
lemma back_run (L R : List Symbol) (a : Symbol) (ha : a≠0)
    (hL : ∀ b∈L,b≠0) :
    MachineCost.run (TM1.step incrementProgram) (L.length+2) (cfg (some true) L (a::R))=
      cfg none [] (L.reverse++a::R) := by
  induction L generalizing a R with
  | nil =>
    rw [show ([]:List Symbol).length+2=2 from rfl]
    rw [show 2=1+1 from rfl,MachineCost.run,back_step _ _ _ ha]
    simp [MachineCost.run,advance,TM1.step,incrementProgram,TM1.stepAux,cfg,
      Tape.mk₂,Tape.mk',Tape.move,ListBlank.cons_mk]
    apply Quotient.sound
    exact Or.inr ⟨1,rfl⟩
  | cons b L ih =>
    have hb : b≠0:=hL b (by simp)
    have hL' : ∀ c∈L,c≠0:=fun c hc=>hL c (by simp [hc])
    rw [List.length_cons,Nat.succ_add,MachineCost.run,back_step _ _ _ ha]
    simpa only [cfg,Tape.mk₂,Tape.move_left_mk',ListBlank.head_mk,ListBlank.tail_mk,
      List.headI_cons,List.tail_cons,ListBlank.cons_mk,List.reverse_cons,List.append_assoc,
      List.singleton_append] using ih (a::R) b hb hL'
lemma carry_false (L : List Symbol) (bs : List Bool) :
    advance (TM1.step incrementProgram) (cfg (some false) L (numeral (false::bs)))=
      cfg (some true) L (2::numeral bs) := by
  simp [advance,TM1.step,incrementProgram,TM1.stepAux,cfg,numeral,Tape.mk₂,Tape.mk',Tape.write]
lemma carry_true (L : List Symbol) (bs : List Bool) :
    advance (TM1.step incrementProgram) (cfg (some false) L (numeral (true::bs)))=
      cfg (some false) (1::L) (numeral bs) := by
  simp [advance,TM1.step,incrementProgram,TM1.stepAux,cfg,numeral,Tape.mk₂,Tape.mk',Tape.write,Tape.move]
lemma carry_nil (L : List Symbol) :
    advance (TM1.step incrementProgram) (cfg (some false) L (numeral []))=
      cfg (some true) L [2,3] := by
  simp [advance,TM1.step,incrementProgram,TM1.stepAux,cfg,numeral,Tape.mk₂,Tape.mk',Tape.write,Tape.move]
lemma increment_run (bs : List Bool) (L : List Symbol) (hL : ∀ b∈L,b≠0) :
    ∃ k≤2*bs.length+L.length+3,
      MachineCost.run (TM1.step incrementProgram) k (cfg (some false) L (numeral bs))=
        cfg none [] (L.reverse++numeral (incrementBits bs)) := by
  induction bs generalizing L with
  | nil =>
    refine ⟨(L.length+2)+1,by simp,?_⟩
    rw [MachineCost.run,carry_nil]
    exact back_run L [3] 2 (by decide) hL
  | cons b bs ih =>
    cases b with
    | false =>
      refine ⟨(L.length+2)+1,by simp,?_⟩
      rw [MachineCost.run,carry_false]
      exact back_run L (numeral bs) 2 (by decide) hL
    | true =>
      have hL' : ∀ b∈(1:Symbol)::L,b≠0 := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl|hb
        · decide
        · exact hL b hb
      obtain ⟨k,hk,he⟩:=ih (1::L) hL'
      refine ⟨k+1,by simp only [List.length_cons] at *; omega,?_⟩
      rw [MachineCost.run,carry_true,he]
      simp [cfg,numeral,incrementBits,List.reverse_cons,List.append_assoc]
theorem increment_natural (n : ℕ) : ∃ k≤2*n.size+3,
    MachineCost.run (TM1.step incrementProgram) k (TM1.init (encodeNat n))=
      cfg none [] (encodeNat (n+1)) := by
  obtain ⟨k,hk,he⟩:=increment_run n.bits [] (by simp)
  refine ⟨k,by simpa only [List.length_nil,Nat.add_zero,Nat.size_eq_bits_len] using hk,?_⟩
  have hi : TM1.init (encodeNat n)=cfg (some false) [] (encodeNat n) := rfl
  rw [hi]
  simpa only [List.reverse_nil,List.nil_append,incrementBits_bits,numeral,encodeNat] using he
lemma incrementProgram_cost : programCost incrementProgram≤5 := by
  apply Finset.sup_le
  intro b _
  cases b <;> decide

theorem increment_post (n : ℕ) (bits : Fin (10*n.size+17) → Bool) :
    (MatchingFPRAS.run (PostCompiler.compiled incrementProgram) (encodeNat n) bits).state=none ∧
    (MatchingFPRAS.run (PostCompiler.compiled incrementProgram) (encodeNat n) bits).tape.right₀=
      ListBlank.mk (encodeNat (n+1)) := by
  obtain ⟨k,hk,he⟩:=increment_natural n
  apply PostCompiler.compiled_words incrementProgram (encodeNat n) (encodeNat (n+1)) k
  · rw [he]
  · rw [he]
    change (Tape.mk₁ (encodeNat (n+1))).right₀=ListBlank.mk _
    exact Tape.mk'_right₀ _ _
  · have hc:=incrementProgram_cost
    calc
      programCost incrementProgram*k+2 ≤ 5*(2*n.size+3)+2 :=
        Nat.add_le_add_right (Nat.mul_le_mul hc hk) 2
      _ = 10*n.size+17 := by ring
end MatchingFPRAS.BinaryArithmetic

end OAI

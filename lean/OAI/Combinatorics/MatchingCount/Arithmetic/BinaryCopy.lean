import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.GuardMachineBase

namespace OAI

namespace MatchingFPRAS.BinaryArithmetic
open Turing MachineCost

inductive CopyPhase
  | seek | append (b : Bool) | rewind | finish | restore
  deriving DecidableEq, Fintype, Inhabited

def bitSymbol (b : Bool) : Symbol := if b then 2 else 1
def markSymbol (b : Bool) : Symbol := if b then 5 else 4
def unmarkSymbol (a : Symbol) : Symbol := if a=4 then 1 else if a=5 then 2 else a
lemma bitSymbol_ne_zero (b : Bool) : bitSymbol b≠0 := by cases b <;> decide
lemma markSymbol_ne_zero (b : Bool) : markSymbol b≠0 := by cases b <;> decide
@[simp] lemma unmark_mark (b : Bool) : unmarkSymbol (markSymbol b)=bitSymbol b := by cases b <;> decide
@[simp] lemma unmark_bit (b : Bool) : unmarkSymbol (bitSymbol b)=bitSymbol b := by cases b <;> decide
@[simp] lemma unmark_three : unmarkSymbol 3=3 := by decide

def copyProgram : CopyPhase → TM1.Stmt Symbol CopyPhase Unit
  | .seek => .branch (fun a _=>a==4 || a==5) (.move .right (.goto (fun _ _=>.seek)))
      (.branch (fun a _=>a==1) (.write (fun _ _=>4) (.goto (fun _ _=>.append false)))
        (.branch (fun a _=>a==2) (.write (fun _ _=>5) (.goto (fun _ _=>.append true)))
          (.move .right (.goto (fun _ _=>.finish)))))
  | .append b => .branch (fun a _=>a==0)
      (.write (fun _ _=>bitSymbol b) (.goto (fun _ _=>.rewind)))
      (.move .right (.goto (fun _ _=>.append b)))
  | .rewind => .branch (fun a _=>a==0)
      (.move .right (.goto (fun _ _=>.seek))) (.move .left (.goto (fun _ _=>.rewind)))
  | .finish => .branch (fun a _=>a==0)
      (.write (fun _ _=>3) (.goto (fun _ _=>.restore)))
      (.move .right (.goto (fun _ _=>.finish)))
  | .restore => .branch (fun a _=>a==0) (.move .right .halt)
      (.write (fun a _=>unmarkSymbol a) (.move .left (.goto (fun _ _=>.restore))))
abbrev copyCfg (s : Option CopyPhase) (L R : List Symbol) : TM1.Cfg Symbol CopyPhase Unit :=
  ⟨s,(),Tape.mk₂ L R⟩
lemma seek_marks (P : List Bool) (L R : List Symbol) :
    MachineCost.run (TM1.step copyProgram) P.length (copyCfg (some .seek) L (P.map markSymbol++R))=
      copyCfg (some .seek) ((P.map markSymbol).reverse++L) R := by
  induction P generalizing L with
  | nil => simp [MachineCost.run,copyCfg]
  | cons b P ih =>
    rw [List.length_cons,MachineCost.run]
    have hs : advance (TM1.step copyProgram) (copyCfg (some .seek) L ((b::P).map markSymbol++R))=
        copyCfg (some .seek) (markSymbol b::L) (P.map markSymbol++R) := by
      cases b <;> simp [advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,markSymbol,Tape.mk₂,Tape.mk',Tape.move]
    rw [hs,ih]
    simp [copyCfg,List.reverse_cons,List.append_assoc]
lemma seek_bit (b : Bool) (L R : List Symbol) :
    advance (TM1.step copyProgram) (copyCfg (some .seek) L (bitSymbol b::R))=
      copyCfg (some (.append b)) L (markSymbol b::R) := by
  cases b <;> simp [advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,markSymbol,bitSymbol,Tape.mk₂,Tape.mk',Tape.write]
lemma append_run (b : Bool) (R L : List Symbol) (hR : ∀ a∈R,a≠0) :
    MachineCost.run (TM1.step copyProgram) (R.length+1) (copyCfg (some (.append b)) L R)=
      copyCfg (some .rewind) (R.reverse++L) [bitSymbol b] := by
  induction R generalizing L with
  | nil => simp [MachineCost.run,advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,Tape.mk₂,Tape.mk',Tape.write]
  | cons a R ih =>
    have ha : (a==0)=false := beq_eq_false_iff_ne.mpr (hR a (by simp))
    rw [List.length_cons,Nat.succ_add,MachineCost.run]
    have hs : advance (TM1.step copyProgram) (copyCfg (some (.append b)) L (a::R))=
        copyCfg (some (.append b)) (a::L) R := by
      simp [advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,Tape.mk₂,Tape.mk',Tape.move,ha]
    rw [hs,ih _ (fun c hc=>hR c (by simp [hc]))]
    simp [copyCfg,List.reverse_cons,List.append_assoc]
lemma rewind_run (L R : List Symbol) (a : Symbol) (ha : a≠0) (hL : ∀ b∈L,b≠0) :
    MachineCost.run (TM1.step copyProgram) (L.length+2) (copyCfg (some .rewind) L (a::R))=
      copyCfg (some .seek) [] (L.reverse++a::R) := by
  have ha' : (a==0)=false := beq_eq_false_iff_ne.mpr ha
  induction L generalizing a R with
  | nil =>
    simp [MachineCost.run,advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,
      Tape.mk₂,Tape.mk',Tape.move,ha',ListBlank.cons_mk]
    apply Quotient.sound
    exact Or.inr ⟨1,rfl⟩
  | cons b L ih =>
    have hb : b≠0:=hL b (by simp)
    rw [List.length_cons,Nat.succ_add,MachineCost.run]
    have hs : advance (TM1.step copyProgram) (copyCfg (some .rewind) (b::L) (a::R))=
        copyCfg (some .rewind) L (b::a::R) := by
      simp [advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,Tape.mk₂,Tape.mk',Tape.move,ha']
    rw [hs,ih (a::R) b hb (fun c hc=>hL c (by simp [hc])) (beq_eq_false_iff_ne.mpr hb)]
    simp [copyCfg,List.reverse_cons,List.append_assoc]

lemma finish_run (R L : List Symbol) (hR : ∀ a∈R,a≠0) :
    MachineCost.run (TM1.step copyProgram) (R.length+1) (copyCfg (some .finish) L R)=
      copyCfg (some .restore) (R.reverse++L) [3] := by
  induction R generalizing L with
  | nil => simp [MachineCost.run,advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,Tape.mk₂,Tape.mk',Tape.write]
  | cons a R ih =>
    have ha : (a==0)=false := beq_eq_false_iff_ne.mpr (hR a (by simp))
    rw [List.length_cons,Nat.succ_add,MachineCost.run]
    have hs : advance (TM1.step copyProgram) (copyCfg (some .finish) L (a::R))=
        copyCfg (some .finish) (a::L) R := by
      simp [advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,Tape.mk₂,Tape.mk',Tape.move,ha]
    rw [hs,ih _ (fun c hc=>hR c (by simp [hc]))]
    simp [copyCfg,List.reverse_cons,List.append_assoc]
lemma restore_run (L R : List Symbol) (a : Symbol) (ha : a≠0) (hL : ∀ b∈L,b≠0) :
    MachineCost.run (TM1.step copyProgram) (L.length+2) (copyCfg (some .restore) L (a::R))=
      copyCfg none [] (L.reverse.map unmarkSymbol++unmarkSymbol a::R) := by
  have ha' : (a==0)=false := beq_eq_false_iff_ne.mpr ha
  induction L generalizing a R with
  | nil =>
    simp [MachineCost.run,advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,
      Tape.mk₂,Tape.mk',Tape.move,Tape.write,ha',ListBlank.cons_mk]
    apply Quotient.sound
    exact Or.inr ⟨1,rfl⟩
  | cons b L ih =>
    have hb : b≠0:=hL b (by simp)
    rw [List.length_cons,Nat.succ_add,MachineCost.run]
    have hs : advance (TM1.step copyProgram) (copyCfg (some .restore) (b::L) (a::R))=
        copyCfg (some .restore) L (b::unmarkSymbol a::R) := by
      simp [advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,Tape.mk₂,Tape.mk',Tape.move,Tape.write,ha']
    rw [hs,ih (unmarkSymbol a::R) b hb (fun c hc=>hL c (by simp [hc])) (beq_eq_false_iff_ne.mpr hb)]
    simp [copyCfg,List.reverse_cons,List.append_assoc]
def copyWord (P Q : List Bool) : List Symbol := P.map markSymbol++Q.map bitSymbol++[3]++P.map bitSymbol
lemma copy_cycle (P Q : List Bool) (b : Bool) :
    MachineCost.run (TM1.step copyProgram) (4*P.length+2*Q.length+8)
      (copyCfg (some .seek) [] (copyWord P (b::Q)))=
      copyCfg (some .seek) [] (copyWord (P++[b]) Q) := by
  let L:=(P.map markSymbol).reverse
  let R:=markSymbol b::(Q.map bitSymbol++[3]++P.map bitSymbol)
  have hR : ∀ a∈R,a≠0 := by
    intro a ha
    simp only [R,List.mem_cons,List.mem_append,List.mem_map,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|((⟨c,hc,rfl⟩|rfl)|⟨c,hc,rfl⟩)
    · exact markSymbol_ne_zero _
    · exact bitSymbol_ne_zero _
    · decide
    · exact bitSymbol_ne_zero _
  have hL : ∀ a∈L,a≠0 := by
    intro a ha
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp ha)
    exact markSymbol_ne_zero _
  have hRL : ∀ a∈R.reverse++L,a≠0 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact hR a (List.mem_reverse.mp ha)
    · exact hL a ha
  have hfirst : MachineCost.run (TM1.step copyProgram) (P.length+1)
      (copyCfg (some .seek) [] (copyWord P (b::Q)))=
      copyCfg (some (.append b)) L R := by
    rw [run_add]
    have he : copyWord P (b::Q)=P.map markSymbol++(bitSymbol b::(Q.map bitSymbol++[3]++P.map bitSymbol)) := by
      simp [copyWord,List.append_assoc]
    rw [he,seek_marks]
    simpa only [MachineCost.run,List.append_nil] using seek_bit b L (Q.map bitSymbol++[3]++P.map bitSymbol)
  have hrun : MachineCost.run (TM1.step copyProgram)
      ((P.length+1)+(R.length+1)+((R.reverse++L).length+2))
        (copyCfg (some .seek) [] (copyWord P (b::Q)))=
        copyCfg (some .seek) [] (copyWord (P++[b]) Q) := by
    rw [run_add _ ((P.length+1)+(R.length+1)) ((R.reverse++L).length+2),
      run_add _ (P.length+1) (R.length+1),hfirst,append_run b R L hR,
      rewind_run (R.reverse++L) [] (bitSymbol b) (bitSymbol_ne_zero b) hRL]
    simp [copyWord,R,L,List.reverse_append,List.append_assoc]
  have hlen : (P.length+1)+(R.length+1)+((R.reverse++L).length+2)=
      4*P.length+2*Q.length+8 := by simp [R,L]; omega
  rw [hlen] at hrun
  exact hrun

lemma copy_finish (P : List Bool) :
    MachineCost.run (TM1.step copyProgram) (4*P.length+5)
      (copyCfg (some .seek) [] (copyWord P []))=
      copyCfg none [] ((P.map bitSymbol++[3])++(P.map bitSymbol++[3])) := by
  let R:=P.map bitSymbol
  let L:=(3:Symbol)::(P.map markSymbol).reverse
  have hR : ∀ a∈R,a≠0 := by
    intro a ha
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp ha
    exact bitSymbol_ne_zero _
  have hRL : ∀ a∈R.reverse++L,a≠0 := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact hR a (List.mem_reverse.mp ha)
    · rcases List.mem_cons.mp ha with rfl|ha
      · decide
      · obtain ⟨c,hc,rfl⟩:=List.mem_map.mp (List.mem_reverse.mp ha)
        exact markSymbol_ne_zero _
  have hfirst : MachineCost.run (TM1.step copyProgram) (P.length+1)
      (copyCfg (some .seek) [] (copyWord P []))=copyCfg (some .finish) L R := by
    rw [run_add]
    have he : copyWord P []=P.map markSymbol++(3::R) := by simp [copyWord,R,List.append_assoc]
    rw [he,seek_marks]
    simp [MachineCost.run,advance,TM1.step,TM1.stepAux,copyProgram,copyCfg,Tape.mk₂,Tape.mk',Tape.move,L]
  have hrun : MachineCost.run (TM1.step copyProgram)
      ((P.length+1)+(R.length+1)+((R.reverse++L).length+2))
        (copyCfg (some .seek) [] (copyWord P []))=
        copyCfg none [] ((P.map bitSymbol++[3])++(P.map bitSymbol++[3])) := by
    rw [run_add _ ((P.length+1)+(R.length+1)) ((R.reverse++L).length+2),
      run_add _ (P.length+1) (R.length+1),hfirst,finish_run R L hR,
      restore_run (R.reverse++L) [] 3 (by decide) hRL]
    simp [R,L,List.reverse_append,List.map_map,Function.comp_def,List.append_assoc]
  have hlen : (P.length+1)+(R.length+1)+((R.reverse++L).length+2)=4*P.length+5 := by
    simp [R,L]
    omega
  rw [hlen] at hrun
  exact hrun
lemma copy_run (P Q : List Bool) :
    ∃ k≤8*(P.length+Q.length+1)*(Q.length+1),
      MachineCost.run (TM1.step copyProgram) k (copyCfg (some .seek) [] (copyWord P Q))=
        copyCfg none [] (((P++Q).map bitSymbol++[3])++((P++Q).map bitSymbol++[3])) := by
  induction Q generalizing P with
  | nil =>
    refine ⟨4*P.length+5,by simp; omega,?_⟩
    simpa using copy_finish P
  | cons b Q ih =>
    obtain ⟨k,hk,he⟩:=ih (P++[b])
    refine ⟨(4*P.length+2*Q.length+8)+k,?_,?_⟩
    · simp only [List.length_append,List.length_cons,List.length_nil] at *
      nlinarith
    · rw [run_add,copy_cycle,he]
      simp [List.append_assoc]
lemma copy_natural (n : ℕ) : ∃ k≤8*(n.size+1)^2,
    MachineCost.run (TM1.step copyProgram) k (TM1.init (encodeNat n))=
      copyCfg none [] (encodeNat n++encodeNat n) := by
  obtain ⟨k,hk,he⟩:=copy_run [] n.bits
  refine ⟨k,?_,?_⟩
  · simpa only [List.length_nil,zero_add,Nat.size_eq_bits_len,pow_two,mul_assoc] using hk
  · have hi : TM1.init (encodeNat n)=copyCfg (some .seek) [] (encodeNat n) := rfl
    rw [hi]
    have henc : n.bits.map bitSymbol++[3]=encodeNat n := rfl
    simpa only [copyWord,List.map_nil,List.nil_append,List.append_nil,henc] using he
lemma copyProgram_cost : programCost copyProgram≤3 := by
  apply Finset.sup_le
  intro p _
  cases p with
  | append b => cases b <;> decide
  | _ => decide

theorem copy_post (n : ℕ) (bits : Fin (24*(n.size+1)^2+2) → Bool) :
    (MatchingFPRAS.run (PostCompiler.compiled copyProgram) (encodeNat n) bits).state=none ∧
    (MatchingFPRAS.run (PostCompiler.compiled copyProgram) (encodeNat n) bits).tape.right₀=
      ListBlank.mk (encodeNat n++encodeNat n) := by
  obtain ⟨k,hk,he⟩:=copy_natural n
  apply PostCompiler.compiled_words copyProgram (encodeNat n) (encodeNat n++encodeNat n) k
  · rw [he]
  · rw [he]
    change (Tape.mk₁ (encodeNat n++encodeNat n)).right₀=ListBlank.mk _
    exact Tape.mk'_right₀ _ _
  · have hc:=copyProgram_cost
    calc
      programCost copyProgram*k+2≤3*(8*(n.size+1)^2)+2 :=
        Nat.add_le_add_right (Nat.mul_le_mul hc hk) 2
      _=24*(n.size+1)^2+2 := by ring
end MatchingFPRAS.BinaryArithmetic

end OAI

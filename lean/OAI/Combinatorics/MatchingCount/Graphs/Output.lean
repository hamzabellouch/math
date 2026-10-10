import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.GuardMachineBase

namespace OAI

namespace MatchingFPRAS.ZeroOutput
open Turing MachineCost

def program (s : Fin 3) : TM1.Stmt Symbol (Fin 3) Unit :=
  if s=0 then .move .left (.write (fun _ _=>6) (.move .right (.goto (fun _ _=>1))))
  else if s=1 then .branch (fun a _=>a==0) (.goto (fun _ _=>2))
    (.write (fun _ _=>0) (.move .right (.goto (fun _ _=>1))))
  else .branch (fun a _=>a==6)
    (.write (fun _ _=>0) (.move .right
      (.write (fun _ _=>4) (.move .right
      (.write (fun _ _=>3) (.move .right
      (.write (fun _ _=>2) (.move .right
      (.write (fun _ _=>3) (.move .left (.move .left (.move .left .halt))))))))))))
    (.move .left (.goto (fun _ _=>2)))
abbrev cfg (s : Option (Fin 3)) (L R : List Symbol) : TM1.Cfg Symbol (Fin 3) Unit :=
  ⟨s,(),Tape.mk₂ L R⟩
lemma zero_blank : ListBlank.mk [(0:Symbol)]=ListBlank.mk [] := by
  apply Quotient.sound
  exact Or.inr ⟨1,rfl⟩
lemma start (input : List Symbol) :
    advance (TM1.step program) (TM1.init input)=cfg (some 1) [6] input := by
  simp [advance,TM1.step,program,TM1.stepAux,TM1.init,cfg,Tape.mk₁,Tape.mk₂,Tape.mk',Tape.move,Tape.write]
lemma erase_step (a : Symbol) (L R : List Symbol) (ha : a≠0) :
    advance (TM1.step program) (cfg (some 1) L (a::R))=cfg (some 1) (0::L) R := by
  have hb : (a==0)=false := by simpa using ha
  simp [advance,TM1.step,program,TM1.stepAux,cfg,Tape.mk₂,Tape.mk',Tape.move,Tape.write,hb]
lemma erase_run (input : List Symbol) (L : List Symbol) (h : ∀ a∈input,a≠0) :
    MachineCost.run (TM1.step program) input.length (cfg (some 1) L input)=
      cfg (some 1) (List.replicate input.length 0++L) [] := by
  induction input generalizing L with
  | nil => rfl
  | cons a input ih =>
    have ha : a≠0:=h a (by simp)
    have hi : ∀ b∈input,b≠0:=fun b hb=>h b (by simp [hb])
    rw [List.length_cons,MachineCost.run,erase_step a L input ha,ih (0::L) hi]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
lemma switch (L : List Symbol) :
    advance (TM1.step program) (cfg (some 1) L [])=cfg (some 2) L [] := by
  simp [advance,TM1.step,program,TM1.stepAux,cfg,Tape.mk₂,Tape.mk']
lemma return_step (L : List Symbol) :
    advance (TM1.step program) (cfg (some 2) (0::L) [])=cfg (some 2) L [] := by
  simp [advance,TM1.step,program,TM1.stepAux,cfg,Tape.mk₂,Tape.mk',Tape.move]
  exact zero_blank
lemma return_run (n : ℕ) :
    MachineCost.run (TM1.step program) n (cfg (some 2) (List.replicate n 0++[6]) [])=
      cfg (some 2) [6] [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append,MachineCost.run,return_step,ih]
lemma return_finish :
    MachineCost.run (TM1.step program) 2 (cfg (some 2) [6] [])=
      cfg none [] (encodeRat 0) := by
  simp [MachineCost.run,advance,TM1.step,program,TM1.stepAux,cfg,Tape.mk₂,Tape.mk',Tape.move,Tape.write,
    encodeRat,encodeInt,encodeNat,Nat.bits]
  exact zero_blank

theorem run_zero (input : List Symbol) (h : ∀ a∈input,a≠0) :
    MachineCost.run (TM1.step program) (2*input.length+4) (TM1.init input)=
      cfg none [] (encodeRat 0) := by
  have heq : 2*input.length+4=1+input.length+1+(input.length+2) := by omega
  rw [heq,run_add _ (1+input.length+1) (input.length+2),run_add _ (1+input.length) 1,
    run_add _ 1 input.length]
  change MachineCost.run (TM1.step program) (input.length+2) (advance (TM1.step program)
    (MachineCost.run (TM1.step program) input.length (advance (TM1.step program) (TM1.init input)))) = _
  rw [start,erase_run input [6] h,switch,run_add,return_run,return_finish]
lemma cost_bound : programCost program ≤ 13 := by
  apply Finset.sup_le
  intro s _
  fin_cases s <;> decide

theorem post_zero (input : List Symbol) (h : ∀ a∈input,a≠0)
    (bits : Fin (26*input.length+54) → Bool) :
    Outputs (PostCompiler.compiled program) input bits 0 := by
  have he:=run_zero input h
  apply PostCompiler.compiled_outputs program input (2*input.length+4)
  · rw [he]
  · rw [he]
    exact Tape.mk'_right₀ _ _
  · calc
      programCost program*(2*input.length+4)+2 ≤ 13*(2*input.length+4)+2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ cost_bound) 2
      _ = 26*input.length+54 := by ring
lemma encodeNat_nonblank (n : ℕ) : ∀ a ∈ encodeNat n,a ≠ 0 := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
    split <;> decide
  · simp only [List.mem_singleton] at ha
    subst a
    decide
lemma encodeInt_nonblank (z : ℤ) : ∀ a ∈ encodeInt z,a ≠ 0 := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · split_ifs at ha <;> simp only [List.mem_singleton] at ha <;> subst a <;> decide
  · exact encodeNat_nonblank _ a ha
lemma encodeRat_nonblank (q : ℚ) : ∀ a ∈ encodeRat q,a ≠ 0 := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact encodeInt_nonblank _ a ha
  · exact encodeNat_nonblank _ a ha
lemma encodeInput_nonblank (G : GraphInput) (ε δ : ℚ) :
    ∀ a ∈ encodeInput G ε δ,a ≠ 0 := by
  intro a ha
  simp only [encodeInput,List.mem_append] at ha
  rcases ha with (((ha|ha)|ha)|ha)|ha
  · exact encodeNat_nonblank _ a ha
  · exact encodeNat_nonblank _ a ha
  · obtain ⟨e,he,ha⟩:=List.mem_flatMap.mp ha
    rcases List.mem_append.mp ha with ha | ha
    · exact encodeNat_nonblank _ a ha
    · exact encodeNat_nonblank _ a ha
  · exact encodeRat_nonblank _ a ha
  · exact encodeRat_nonblank _ a ha

theorem post_zero_input (G : GraphInput) (ε δ : ℚ)
    (bits : Fin (26*(encodeInput G ε δ).length+54) → Bool) :
    Outputs (PostCompiler.compiled program) (encodeInput G ε δ) bits 0 :=
  post_zero _ (encodeInput_nonblank G ε δ) bits
end MatchingFPRAS.ZeroOutput

end OAI

import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.BinaryAddition
import OAI.Combinatorics.MatchingCount.Tapes.StackWords
import OAI.Combinatorics.MatchingCount.Tapes.FixedEncoding

namespace OAI

namespace MatchingFPRAS.PostAddition
open Turing StackAddition

local instance initialCarry : Inhabited Bool := ⟨false⟩
abbrev Alphabet := TM2to1.Γ' (Fin 3) (fun _=>Bool)
noncomputable def machine : RandomMachine :=
  StackWords.compiled (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    program Finset.univ finite_support
noncomputable def overhead : ℕ :=
  StackWords.cost (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    program Finset.univ
noncomputable def input (A B : List Bool) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet) (stackData A B []) (A.length+B.length)
noncomputable def output (A B : List Bool) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet)
    (stackData [] [] (addDigits false A B).reverse) (A.length+B.length+1)
noncomputable def steps (A B : List Bool) : ℕ :=
  overhead*((A.length+B.length+1)*(1+6*(A.length+B.length+3*(A.length+B.length+1)+1)))+2

theorem computes (A B : List Bool) (t : ℕ) (ht : steps A B≤t) (bits : Fin t → Bool) :
    (run machine (input A B) bits).state=none ∧
    (run machine (input A B) bits).tape.right₀=ListBlank.mk (output A B) := by
  obtain ⟨n,hn,hr⟩:=run_addition A B [] false default
  have h₀ : StackCost.StackBound (stackData A B []) (A.length+B.length) := by
    intro i
    fin_cases i <;> simp [stackData]
  have he : MachineCost.run (TM2.step program) n
      ⟨some (default : Bool),(default : Store),stackData A B []⟩=
        cfg none [] [] (addDigits false A B).reverse default := by
    change MachineCost.run (TM2.step program) n (cfg (some false) A B [] default)=_
    simpa only [List.append_nil] using hr
  have hh : (MachineCost.run (TM2.step program) n
      ⟨some (default : Bool),(default : Store),stackData A B []⟩).l=none := by rw [he]; rfl
  have ho : StackCost.StackBound (MachineCost.run (TM2.step program) n
      ⟨some (default : Bool),(default : Store),stackData A B []⟩).stk (A.length+B.length+1) := by
    rw [he]
    intro i
    have hl:=addDigits_length A B false
    fin_cases i <;> simp [cfg,stackData]
    omega
  have htime : StackWords.cost (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
      program Finset.univ*(n*(1+2*3*(A.length+B.length+n*3+1)))+2≤t := by
    apply le_trans _ ht
    unfold steps overhead
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul hn
    omega
  have hc:=StackWords.compiled_execution (FixedEncoding.enc Alphabet)
    (FixedEncoding.dec Alphabet) (FixedEncoding.blank Alphabet) (FixedEncoding.left_inverse Alphabet)
    program Finset.univ finite_support 3 accesses_bound
    (stackData A B []) (A.length+B.length) h₀ n (A.length+B.length+1) hh ho t htime bits
  change (run machine (input A B) bits).state=none ∧
    (run machine (input A B) bits).tape.right₀=ListBlank.mk
      (StackWords.encoded (FixedEncoding.enc Alphabet)
        (MachineCost.run (TM2.step program) n
          ⟨some (default : Bool),(default : Store),stackData A B []⟩).stk
          (A.length+B.length+1)) at hc
  rw [he] at hc
  exact hc
lemma result_value (m n : ℕ) :
    value ((addDigits false m.bits n.bits).reverse.reverse)=m+n := by
  simpa only [List.reverse_reverse] using addition_numerals m n
lemma time_quadratic (A B : List Bool) :
    steps A B=overhead*(24*(A.length+B.length)^2+49*(A.length+B.length)+25)+2 := by
  unfold steps
  ring
end MatchingFPRAS.PostAddition

end OAI

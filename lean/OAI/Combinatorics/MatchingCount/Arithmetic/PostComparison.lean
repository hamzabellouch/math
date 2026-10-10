import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.StackWords
import OAI.Combinatorics.MatchingCount.Tapes.FixedEncoding
import OAI.Combinatorics.MatchingCount.Arithmetic.BinaryCompare

namespace OAI

namespace MatchingFPRAS.PostComparison
open Turing StackCompare

local instance initialOrder : Inhabited Ordering := ⟨.eq⟩
abbrev Alphabet := TM2to1.Γ' (Fin 3) (fun _=>Bool)
lemma support : TM2.Supports program Finset.univ := by
  simp [TM2.Supports,program,TM2.SupportsStmt]
noncomputable def machine : RandomMachine :=
  StackWords.compiled (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    program Finset.univ support
noncomputable def overhead : ℕ :=
  StackWords.cost (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    program Finset.univ
noncomputable def input (A B : List Bool) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet) (StackAddition.stackData A B []) (A.length+B.length)
noncomputable def output (c : Ordering) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet)
    (StackAddition.stackData [] [] (flags c)) 2
noncomputable def steps (A B : List Bool) : ℕ :=
  overhead*((A.length+B.length+1)*(1+8*(A.length+B.length+4*(A.length+B.length+1)+1)))+2

theorem computes (A B : List Bool) (t : ℕ) (ht : steps A B≤t) (bits : Fin t → Bool) :
    (run machine (input A B) bits).state=none ∧
    (run machine (input A B) bits).tape.right₀=
      ListBlank.mk (output (compare (StackAddition.value A) (StackAddition.value B))) := by
  obtain ⟨n,hn,hr⟩:=run_comparison A B [] .eq default
  have h₀ : StackCost.StackBound (StackAddition.stackData A B []) (A.length+B.length) := by
    intro i
    fin_cases i <;> simp [StackAddition.stackData]
  have he : MachineCost.run (TM2.step program) n
      ⟨some (default : Ordering),(default : StackAddition.Store),StackAddition.stackData A B []⟩=
        cfg none [] [] (flags (compareDigits .eq A B)) default := by
    change MachineCost.run (TM2.step program) n (cfg (some .eq) A B [] default)=_
    simpa only [List.append_nil] using hr
  have hh : (MachineCost.run (TM2.step program) n
      ⟨some (default : Ordering),(default : StackAddition.Store),StackAddition.stackData A B []⟩).l=none := by rw [he]; rfl
  have ho : StackCost.StackBound (MachineCost.run (TM2.step program) n
      ⟨some (default : Ordering),(default : StackAddition.Store),StackAddition.stackData A B []⟩).stk 2 := by
    rw [he]
    change StackCost.StackBound (StackAddition.stackData [] [] (flags (compareDigits .eq A B))) 2
    intro i
    fin_cases i <;> simp [StackAddition.stackData,flags]
  have htime : StackWords.cost (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
      program Finset.univ*(n*(1+2*4*(A.length+B.length+n*4+1)))+2≤t := by
    apply le_trans _ ht
    unfold steps overhead
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul hn
    omega
  have hc:=StackWords.compiled_execution (FixedEncoding.enc Alphabet)
    (FixedEncoding.dec Alphabet) (FixedEncoding.blank Alphabet) (FixedEncoding.left_inverse Alphabet)
    program Finset.univ support 4 accesses_bound
    (StackAddition.stackData A B []) (A.length+B.length) h₀ n 2 hh ho t htime bits
  change (run machine (input A B) bits).state=none ∧
    (run machine (input A B) bits).tape.right₀=ListBlank.mk
      (StackWords.encoded (FixedEncoding.enc Alphabet)
        (MachineCost.run (TM2.step program) n
          ⟨some (default : Ordering),(default : StackAddition.Store),StackAddition.stackData A B []⟩).stk
          2) at hc
  rw [he,compares_values] at hc
  exact hc
lemma time_quadratic (A B : List Bool) :
    steps A B=overhead*(40*(A.length+B.length)^2+81*(A.length+B.length)+41)+2 := by
  unfold steps
  congr 2
  ring
lemma computes_numerals (m n : ℕ) (t : ℕ) (ht : steps m.bits n.bits≤t) (bits : Fin t → Bool) :
    (run machine (input m.bits n.bits) bits).state=none ∧
    (run machine (input m.bits n.bits) bits).tape.right₀=ListBlank.mk (output (compare m n)) := by
  simpa only [StackAddition.value_bits] using computes m.bits n.bits t ht bits
end MatchingFPRAS.PostComparison

end OAI

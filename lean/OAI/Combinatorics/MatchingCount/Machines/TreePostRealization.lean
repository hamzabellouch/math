import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeSum

namespace OAI

namespace MatchingFPRAS.TreePost
open TreeTyped TreeData TreeFunction TreeMachine RegisterProc Turing Polynomial

abbrev Alphabet := TM2to1.Γ' (K Reg) (fun _=>Bool)
noncomputable def accesses (P : Proc (K Reg)) : ℕ :=
  Finset.univ.sup (fun l=>StackCost.accesses (P.code l))
lemma accesses_bound (P : Proc (K Reg)) (l : P.Label) : StackCost.accesses (P.code l)≤accesses P :=
  Finset.le_sup (f := fun l=>StackCost.accesses (P.code l)) (Finset.mem_univ l)
noncomputable def machine (P : Proc (K Reg)) : RandomMachine :=
  StackWords.compiled (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    P.code Finset.univ (StackComposition.supports_univ P.code)
noncomputable def overhead (P : Proc (K Reg)) : ℕ :=
  StackWords.cost (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet) P.code Finset.univ

def inputStacks {A : Type} [Codec A] (a : A) : Stack (K Reg) :=
  encodeEnv (env (TreeTyped.encode a) .nil .nil)
lemma inputStacks_bound {A : Type} [Codec A] (a : A) : StackCost.StackBound (inputStacks a) (weight a) := by
  intro i
  have h:=weight_pos a
  cases i with
  | inr i => simp [inputStacks,encodeEnv]
  | inl i =>
    simp only [inputStacks,encodeEnv,env]
    split_ifs <;> first
    | exact le_rfl
    | simpa only [TreeData.encode,List.length_singleton] using (Nat.succ_le_iff.mpr h)

noncomputable def packed {A : Type} [Codec A] (a : A) : List Symbol :=
  StackWords.encoded (FixedEncoding.enc Alphabet) (inputStacks a) (weight a)
noncomputable def steps {A B : Type} [Codec A] [Codec B] {f : A→B} (F : Realizer f) (a : A) : ℕ :=
  overhead F.program*(F.cost a*(1+2*accesses F.program*(weight a+F.cost a*accesses F.program+1)))+2

theorem computes {A B : Type} [Codec A] [Codec B] {f : A→B} (F : Realizer f)
    (a : A) (t : ℕ) (ht : steps F a≤t) (bits : Fin t→Bool) :
    (run (machine F.program) (packed a) bits).state=none ∧
    (run (machine F.program) (packed a) bits).tape.right₀=ListBlank.mk (packed (f a)) := by
  obtain ⟨n,hn,he⟩:=F.correct a .nil
  change MachineCost.run (TM2.step F.program.code) n
      ⟨some default,default,inputStacks a⟩=⟨none,none,inputStacks (f a)⟩ at he
  have hh : (MachineCost.run (TM2.step F.program.code) n
      ⟨some default,default,inputStacks a⟩).l=none := by rw [he]
  have ho : StackCost.StackBound (MachineCost.run (TM2.step F.program.code) n
      ⟨some default,default,inputStacks a⟩).stk (weight (f a)) := by
    rw [he]
    exact inputStacks_bound (f a)
  have htime : overhead F.program*(n*(1+2*accesses F.program*(weight a+n*accesses F.program+1)))+2≤t := by
    apply le_trans _ ht
    unfold steps
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.mul_le_mul hn
    gcongr
  have h:=StackWords.compiled_execution (FixedEncoding.enc Alphabet) (FixedEncoding.dec Alphabet)
    (FixedEncoding.blank Alphabet) (FixedEncoding.left_inverse Alphabet)
    F.program.code Finset.univ (StackComposition.supports_univ F.program.code)
    (accesses F.program) (accesses_bound F.program) (inputStacks a) (weight a) (inputStacks_bound a)
    n (weight (f a)) hh ho t htime bits
  rw [he] at h
  exact h

lemma packed_length {A : Type} [Codec A] (a : A) :
    (packed a).length=Fintype.card Alphabet*weight a := by
  have hp:=weight_pos a
  unfold packed StackWords.encoded FixedAlphabetCompiler.word
  rw [List.length_map,FixedEncoding.bitsWord_length]
  congr 1
  change ((StackWords.rows (inputStacks a) (weight a)).tail.map (fun x=>(false,x))).length+1=weight a
  simp only [List.length_map,List.length_tail,StackWords.rows,List.length_ofFn]
  omega
lemma weight_le_packed_length {A : Type} [Codec A] (a : A) : weight a≤(packed a).length := by
  rw [packed_length]
  exact Nat.le_mul_of_pos_left _ Fintype.card_pos

theorem polynomial_compiles {A B : Type} [Codec A] [Codec B] {f : A→B}
    (F : Realizer f) (hF : PolynomialTime F) :
    ∃ p : Polynomial ℕ,∀ a (t : ℕ),p.eval (packed a).length≤t → ∀ bits : Fin t→Bool,
      (run (machine F.program) (packed a) bits).state=none ∧
      (run (machine F.program) (packed a) bits).tape.right₀=ListBlank.mk (packed (f a)) := by
  obtain ⟨p,hp⟩:=hF
  let q : Polynomial ℕ:=C (overhead F.program)*(p*(1+2*C (accesses F.program)*(X+p*C (accesses F.program)+1)))+2
  refine ⟨q,fun a t ht bits=>computes F a t (le_trans ?_ ht) bits⟩
  have hc : F.cost a≤p.eval (weight a):=le_trans (Nat.le_add_right _ _) (hp a)
  have hm:=polynomial_eval_monotone q (weight_le_packed_length a)
  apply le_trans _ hm
  simp only [q,steps,eval_add,eval_mul,eval_C,eval_X,eval_one,eval_ofNat]
  gcongr
end MatchingFPRAS.TreePost

end OAI

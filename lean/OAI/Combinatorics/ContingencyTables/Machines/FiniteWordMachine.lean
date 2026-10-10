import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordExecution
import OAI.Combinatorics.ContingencyTables.Machines.LiteralProgram

namespace OAI

/-! # A single physical machine for a computed finite-word algorithm -/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing
open TreeTyped Polynomial

variable {n : List Symbol → ℕ} {f : List Symbol×List Bool → List Symbol}

noncomputable def machine (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f) : RandomMachine :=
  (LiteralProgram.wrap (realizer N F)).machine

noncomputable def machineTime (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) : ℕ := LiteralProgram.wrapTime (realizer N F) as

private lemma output_alphabet (as : List Symbol)
    (hout : ∀ bs,∀ b∈f (as,bs),b≠6 ∧ b≠7) :
    (experiment n f as).All (fun bs => ∀ b∈bs,b≠6 ∧ b≠7) := by
  unfold experiment
  rw [Experiment.all_map]
  exact (Experiment.all_true _).mono (fun bs _ => hout bs)

/-- Every run halts within the physical execution bound. Its output law
is exactly the law obtained by feeding an independent uniform word to f. -/
theorem machine_law (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ b∈f (as,bs),b≠6 ∧ b≠7)
    (t : ℕ) (ht : machineTime N F as≤t) :
    (∀ bits : Bits t,(run (machine N F) as bits).state=none) ∧
    ∀ g : Tape Symbol → ℚ,
      average (fun bits : Bits t => g (run (machine N F) as bits).tape)=
        average (fun bits : Bits (n as) => g (Tape.mk₁ (f (as,List.ofFn bits)))) := by
  have hr := LiteralProgram.wrap_realizes (realizer N F) as ha (output_alphabet as hout)
  constructor
  · intro bits
    exact (hr.run_all (fun _ => True) (Experiment.all_true _) t ht bits).1
  · intro g
    have hm := hr.run_mean g t ht
    rw [Experiment.mean_map] at hm
    exact hm.trans (experiment_mean n f as (fun bs => g (Tape.mk₁ bs)))

/-- Packing, coin reads, deterministic execution and public output all
have a polynomial bound in encoded input size plus the declared word. -/
theorem machineTime_polynomial {N : TreeTyped.Realizer n} {F : TreeTyped.Realizer f}
    (hN : TreeTyped.PolynomialTime N) (hF : TreeTyped.PolynomialTime F) :
    ∃ q : Polynomial ℕ,∀ as,machineTime N F as≤q.eval (wordMeasure n as) := by
  obtain ⟨p,hp⟩ := work_realizer hN hF
  let G := realizer N F
  let a := OnlineStack.accesses G.program.code
  let o := OnlineStack.overhead G.program.code
  let pk : Polynomial ℕ := (1+LiteralProgram.budgetPolynomial 1 (18*LiteralPacked.width) X 0)*
    C (MachineCost.programCost LiteralPacked.packCode)
  let out : Polynomial ℕ := C (MachineCost.programCost (LiteralTape.eraseCode LiteralPacked.header.length))+
    (1+LiteralProgram.budgetPolynomial (18*LiteralPacked.width) 1 p 0)*
      C (MachineCost.programCost LiteralPacked.unpackCode)
  let fac : Polynomial ℕ := C o*(1+2*C a*(X+p*C a+1))+1
  refine ⟨pk+p*fac+out,fun as => ?_⟩
  let M := wordMeasure n as
  have hw : weight as≤M := Nat.le_add_right _ _
  have hn : as.length≤M := (list_length_le_weight as).trans hw
  have hc : G.cost as≤p.eval M := (Nat.le_add_right _ _).trans (hp as)
  have hout : (experiment n f as).worst weight≤p.eval M :=
    (Nat.le_add_left _ _).trans (hp as)
  have hl : (experiment n f as).worst List.length≤p.eval M :=
    Experiment.worst_le _ _ _ ((Experiment.all_worst _ weight).mono
      (fun bs hbs => (list_length_le_weight bs).trans (hbs.trans hout)))
  have hf : OnlineStack.Executes.factor G.program.code (weight as) (G.cost as)≤fac.eval M := by
    have he : fac.eval M=OnlineStack.Executes.factor G.program.code M (p.eval M) := by
      simp only [fac,eval_add,eval_mul,eval_C,eval_ofNat,eval_X,eval_one,
        OnlineStack.Executes.factor,a,o]
    rw [he]
    exact OnlineStack.Executes.factor_mono _ _ _ _ hw hc
  have hpk : pk.eval M=LiteralProgram.packTime M := by
    simp only [pk,eval_mul,eval_add,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_X,eval_zero,LiteralProgram.packTime]
  have hpout : out.eval M=LiteralProgram.postTime (p.eval M) := by
    simp only [out,eval_add,eval_mul,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_zero,LiteralProgram.postTime]
  change LiteralProgram.wrapTime G as≤(pk+p*fac+out).eval M
  simp only [eval_add,eval_mul,hpk,hpout]
  unfold LiteralProgram.wrapTime OnlineTree.physicalCost
  exact Nat.add_le_add
    (Nat.add_le_add (LiteralProgram.packTime_mono hn) (Nat.mul_le_mul hc hf))
    (LiteralProgram.postTime_mono hl)

end ContingencyTables.FiniteWordExecution

end OAI

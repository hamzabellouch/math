import OAI.Combinatorics.MatchingCount.Tapes.PackedExecution
import OAI.Combinatorics.MatchingCount.Machines.OnlinePhysicalProgram
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProgramMap
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProgramSeal

namespace OAI

/-! # Public binary input and output for typed finite programs

Literal packing is independent of the counting algorithm. Its cost includes every packing, execution, and printing step.
-/

namespace ContingencyTables.LiteralProgram
open MatchingFPRAS Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped Polynomial

noncomputable def pack : Program := Program.ofTM1 packCode .start (fun _ => 0)
noncomputable def erase : Program := Program.ofTM1 (LiteralTape.eraseCode header.length) () ()
noncomputable def unpack : Program := Program.ofTM1 unpackCode .start (fun _ => 0)
noncomputable def post : Program := erase.seq unpack
noncomputable def packTime (n : ℕ) : ℕ :=
  (1+LiteralBlockMap.budget 1 (18*width) n 0)*MachineCost.programCost packCode
noncomputable def postTime (n : ℕ) : ℕ :=
  MachineCost.programCost (LiteralTape.eraseCode header.length)+
    (1+LiteralBlockMap.budget (18*width) 1 n 0)*MachineCost.programCost unpackCode

lemma packTime_mono {n m : ℕ} (h : n ≤ m) : packTime n ≤ packTime m := by
  unfold packTime LiteralBlockMap.budget
  gcongr

lemma postTime_mono {n m : ℕ} (h : n ≤ m) : postTime n ≤ postTime m := by
  unfold postTime LiteralBlockMap.budget
  gcongr

lemma pack_realizes (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    pack.Realizes (Tape.mk₁ as) (.done (Tape.mk₁ (TreePost.packed as))) (packTime as.length) :=
  Program.realizes_TM1 _ _ _ _ _ _ _ (pack_exec as ha)

lemma post_realizes (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    post.Realizes (Tape.mk₁ (TreePost.packed as)) (.done (Tape.mk₁ as)) (postTime as.length) := by
  have h1 : erase.Realizes (Tape.mk₁ (TreePost.packed as))
      (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
      (MachineCost.programCost (LiteralTape.eraseCode header.length)) := by
    rw [packed_eq]
    exact (Program.realizes_TM1 _ _ _ _ _ _ _
      (LiteralTape.erase_exec header (as.reverse.flatMap chunk))).mono (by simp only [Nat.one_mul]; rfl)
  have h2 : unpack.Realizes (Tape.mk₁ (as.reverse.flatMap chunk)) (.done (Tape.mk₁ as))
      ((1+LiteralBlockMap.budget (18*width) 1 as.length 0)*MachineCost.programCost unpackCode) :=
    Program.realizes_TM1 _ _ _ _ _ _ _ (unpack_exec as ha)
  exact Program.seq_realizes erase unpack _ (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
    (fun _ => .done (Tape.mk₁ as)) _ _ h1 h2

noncomputable def wrap {f : List Symbol → Experiment (List Symbol)}
    (F : OnlineTree.Realizer f) : Program := (pack.seq (OnlineTree.physicalProgram F)).seq post

noncomputable def wrapTime {f : List Symbol → Experiment (List Symbol)}
    (F : OnlineTree.Realizer f) (as : List Symbol) : ℕ :=
  packTime as.length+OnlineTree.physicalCost F as+postTime ((f as).worst List.length)

private lemma experiment_all_and {A : Type} {p : Experiment A} {P Q : A → Prop}
    (hp : p.All P) (hq : p.All Q) : p.All (fun a => P a ∧ Q a) := by
  induction p with
  | done a => exact ⟨hp,hq⟩
  | read p ih => exact ⟨ih false hp.1 hq.1,ih true hp.2 hq.2⟩
  | delay n p ih => exact ih hp hq

lemma wrap_realizes {f : List Symbol → Experiment (List Symbol)}
    (F : OnlineTree.Realizer f) (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : (f as).All (fun bs => ∀ b∈bs,b≠6 ∧ b≠7)) :
    (wrap F).Realizes (Tape.mk₁ as) ((f as).map Tape.mk₁) (wrapTime F as) := by
  have h1 : (pack.seq (OnlineTree.physicalProgram F)).Realizes (Tape.mk₁ as)
      ((f as).map (fun bs => Tape.mk₁ (TreePost.packed bs)))
      (packTime as.length+OnlineTree.physicalCost F as) :=
    Program.seq_realizes pack (OnlineTree.physicalProgram F) _ (.done (Tape.mk₁ (TreePost.packed as)))
      (fun _ => (f as).map (fun bs => Tape.mk₁ (TreePost.packed bs))) _ _
      (pack_realizes as ha) (OnlineTree.physical_realizes F as)
  exact Program.seq_realizes_map _ _ _ (f as) (fun bs => Tape.mk₁ (TreePost.packed bs))
    (fun bs => .done (Tape.mk₁ bs)) _ _ h1
    ((experiment_all_and hout (Experiment.all_worst (f as) List.length)).mono
      (fun bs hbs => (post_realizes bs hbs.1).mono (postTime_mono hbs.2)))

/-- A polynomial representing the exact elementary block-map cost. -/
noncomputable def budgetPolynomial (w H : ℕ) (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p+1)*(C (3+w+H)+2*(q+p*C (H+w)))

lemma eval_budgetPolynomial (w H : ℕ) (p q : Polynomial ℕ) (n : ℕ) :
    (budgetPolynomial w H p q).eval n=LiteralBlockMap.budget w H (p.eval n) (q.eval n) := by
  simp only [budgetPolynomial,LiteralBlockMap.budget,eval_mul,eval_add,eval_C,eval_one,eval_ofNat]

/-- Any polynomial bound on the typed experiment gives a polynomial bound
on the complete public binary execution. -/
theorem polynomial_wrap {f : List Symbol → Experiment (List Symbol)}
    (F : OnlineTree.Realizer f) (p : Polynomial ℕ)
    (hp : ∀ as,F.cost as+(f as).worst weight ≤ p.eval (weight as)) :
    ∃ q : Polynomial ℕ,∀ as,wrapTime F as ≤ q.eval as.length := by
  let b : Polynomial ℕ := 18*X+1
  let v := p.comp b
  let a := OnlineStack.accesses F.program.code
  let o := OnlineStack.overhead F.program.code
  let pk : Polynomial ℕ := (1+budgetPolynomial 1 (18*width) X 0)*C (MachineCost.programCost packCode)
  let out : Polynomial ℕ := C (MachineCost.programCost (LiteralTape.eraseCode header.length))+
    (1+budgetPolynomial (18*width) 1 v 0)*C (MachineCost.programCost unpackCode)
  let fac : Polynomial ℕ := C o*(1+2*C a*(b+v*C a+1))+1
  refine ⟨pk+v*fac+out,fun as => ?_⟩
  have hv : v.eval as.length=p.eval (weight as) := by
    simp only [v,b,eval_comp,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,LiteralCodec.weight_word]
  have hc : F.cost as ≤ v.eval as.length := by rw [hv]; exact (Nat.le_add_right _ _).trans (hp as)
  have hw : (f as).worst weight ≤ v.eval as.length := by rw [hv]; exact (Nat.le_add_left _ _).trans (hp as)
  have hl : (f as).worst List.length ≤ v.eval as.length :=
    Experiment.worst_le _ _ _ ((Experiment.all_worst _ weight).mono
      (fun bs hbs => (list_length_le_weight bs).trans (hbs.trans hw)))
  have hf : OnlineStack.Executes.factor F.program.code (weight as) (F.cost as) ≤ fac.eval as.length := by
    have he : fac.eval as.length=OnlineStack.Executes.factor F.program.code (weight as) (v.eval as.length) := by
      simp only [fac,b,eval_add,eval_mul,eval_C,eval_ofNat,eval_one,eval_X,
        OnlineStack.Executes.factor,LiteralCodec.weight_word,a,o]
    rw [he]
    exact OnlineStack.Executes.factor_mono _ _ _ _ le_rfl hc
  have hpk : pk.eval as.length=packTime as.length := by
    simp only [pk,eval_mul,eval_add,eval_one,eval_C,eval_budgetPolynomial,eval_X,eval_zero,packTime]
  have hout : out.eval as.length=postTime (v.eval as.length) := by
    simp only [out,eval_add,eval_mul,eval_one,eval_C,eval_budgetPolynomial,eval_zero,postTime]
  simp only [eval_add,eval_mul,hpk,hout]
  unfold wrapTime OnlineTree.physicalCost
  exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul hc hf) _) (postTime_mono hl)

/-- Deterministic typed programs therefore execute on the public binary
tape with one fixed finite transition table and a polynomial time bound. -/
theorem deterministic_compiles {f : List Symbol → List Symbol}
    (F : TreeTyped.Realizer f) (hF : PolynomialTime F)
    (hout : ∀ as,∀ b∈f as,b≠6 ∧ b≠7) :
    ∃ (A : RandomMachine) (q : Polynomial ℕ),∀ as,(∀ a∈as,a≠0) →
      ∀ t,q.eval as.length ≤ t → ∀ bits : Fin t → Bool,
      (run A as bits).state=none ∧ (run A as bits).tape.right₀=ListBlank.mk (f as) := by
  obtain ⟨p,hp⟩ := hF
  obtain ⟨q,hq⟩ := polynomial_wrap (OnlineTree.deterministic F) p hp
  refine ⟨(wrap (OnlineTree.deterministic F)).machine,q,?_⟩
  intro as ha t ht bits
  have hr := wrap_realizes (OnlineTree.deterministic F) as ha (hout as)
  apply hr.run_all (fun T => T.right₀=ListBlank.mk (f as)) _ t ((hq as).trans ht) bits
  change (Tape.mk₁ (f as)).right₀=ListBlank.mk (f as)
  simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]

end ContingencyTables.LiteralProgram

end OAI

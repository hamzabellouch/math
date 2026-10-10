import OAI.Combinatorics.ContingencyTables.Sampling.ExactTablePrefix

namespace OAI

/-! # The fixed exact-sampling machine on the literal public binary tape -/

namespace ContingencyTables.ExactPublicPrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms
open scoped Classical
noncomputable section

/-- These two finite programs are independent of dimensions and margins. -/
def middle : Program := ExactPhysicalProgram.program.seq LiteralProgram.post
def program : Program := LiteralProgram.pack.seq middle

def machine : RandomMachine := program.machine

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

def word (X : Table r c) : List Symbol := GreedyFeasibleTable.printMatrix (matrixCode X.val)

lemma word_eq (X : Table r c) : word r c X=Algorithms.encodeMatrix X.val :=
  GreedyFeasibleTable.printMatrix_ofFn X.val

def middleOutput : Option (Table r c) → Cfg Symbol middle.State
  | none => leftCfg LiteralProgram.post.entry (ExactTablePrefix.output r c none)
  | some X => rightCfg (LiteralProgram.post.final (Tape.mk₁ (word r c X)))

def output (o : Option (Table r c)) : Cfg Symbol program.State := rightCfg (middleOutput r c o)

lemma middle_prefix (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    ∃ p,Implements middle.table (middleOutput r c)
      (middle.initial (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) p ∧
      ∀ g : Option (Table r c) → ℚ,p.mean g=(ExactTablePrefix.experiment r c N).mean g := by
  obtain ⟨p,hp,hpm⟩ := ExactTablePrefix.physical_prefix r c htotal N
  obtain ⟨q,hq,hqm,_⟩ := PhysicalPartialSequence.left_prefix_injective
    ExactPhysicalProgram.program.table LiteralProgram.post.table LiteralProgram.post.entry
    (ExactTablePrefix.output r c) (ExactTablePrefix.output_injective r c) _ p hp
  have next (o : Option (Table r c)) : ∃ u,
      Implements middle.table (middleOutput r c)
        (leftCfg LiteralProgram.post.entry (ExactTablePrefix.output r c o)) u ∧
      ∀ g : Option (Table r c) → ℚ,u.mean g=g o := by
    cases o with
    | none => exact ⟨.done none,.done none,fun _ => rfl⟩
    | some X =>
      obtain ⟨u,hu,hum,_⟩ := LiteralProgram.post_realizes (word r c X)
        (ProfilePrograms.printMatrix_alphabet _)
      have hu' := hu.right (M := ExactPhysicalProgram.program.table) LiteralProgram.post.entry
      have hall : u.All (fun T => T=Tape.mk₁ (word r c X)) :=
        Experiment.all_of_mean_eq hum _ rfl
      refine ⟨u.map (fun _ => some X),?_,?_⟩
      · have hv := hu'.map_all (fun _ => some X) (middleOutput r c)
          (hall.mono (by intro T hT; rw [hT]; rfl))
        simpa only [middle,Program.seq,ExactTablePrefix.output,ExactTablePrefix.code,Option.map_some,
          ExactPhysicalProgram.output_some,word,leftCfg,Program.final,Program.initial,
          Option.elim_none,rightCfg,Option.map_some] using hv
      · intro g
        rw [Experiment.mean_map,PhysicalPartialSequence.mean_const]
  choose u hu hum using next
  refine ⟨q.bind u,hq.bind u _ hu,?_⟩
  intro g
  rw [Experiment.mean_bind]
  simp_rw [hum]
  exact (hqm g).trans (hpm g)

theorem prefix_correct (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    ∃ p,Implements program.table (output r c)
      (program.initial (Tape.mk₁ (ExactTablePrefix.input r c))) p ∧
      ∀ g : Option (Table r c) → ℚ,p.mean g=(ExactTablePrefix.experiment r c N).mean g := by
  obtain ⟨p,hp,hpm⟩ := middle_prefix r c htotal N
  have hi : ∀ a∈ExactTablePrefix.input r c,a≠0 := by
    intro a ha
    exact GreedyFeasibleTable.encodeMargins_nonzero r c a ha
  obtain ⟨u,hu,hum,_⟩ := LiteralProgram.pack_realizes (ExactTablePrefix.input r c) hi
  obtain ⟨v,hv,hvm,_⟩ := PhysicalPartialSequence.left_prefix LiteralProgram.pack.table middle.table
    middle.entry LiteralProgram.pack.final _ u hu
  have hall : v.All (fun x => x=LiteralProgram.pack.final
      (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) := by
    rw [Experiment.all_indicator,hvm,hum]
    simp only [Experiment.mean,ite_true]
  have hp' := hp.right (M := LiteralProgram.pack.table) middle.entry
  refine ⟨v.bind (fun _ => p),?_,?_⟩
  · apply hv.bind_all (fun _ => p) (output r c)
    exact hall.mono (by intro x hx; rw [hx]; exact hp')
  · intro g
    rw [Experiment.mean_bind,PhysicalPartialSequence.mean_const]
    exact hpm g

lemma output_none_live : (output r c none).state≠none := by
  change (some _ : Option program.State)≠none
  exact Option.some_ne_none _

lemma output_halted (X : Table r c) : (output r c (some X)).state=none := rfl

lemma output_tape (X : Table r c) :
    (output r c (some X)).tape.right₀=ListBlank.mk (Algorithms.encodeMatrix X.val) := by
  change (Tape.mk₁ (word r c X)).right₀=_
  rw [word_eq]
  simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]

end
end ContingencyTables.ExactPublicPrefix

end OAI

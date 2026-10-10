import OAI.Combinatorics.ContingencyTables.Sampling.ExactGatePhysical
import OAI.Combinatorics.ContingencyTables.Sampling.ExactPublicCost

namespace OAI

/-! # The cheap gate prefix on public binary input -/

namespace ContingencyTables.ExactGatePublic
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms ProfilePrograms SmallGraphProfiles
open ExactTablePrefix (code decode code_decode decode_eq_iff input)
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

attribute [local irreducible] exactOrdinary

lemma feasible (htotal : (∑ i,r i)=∑ j,c j) :
    (ExactGatePrefix.experiment (List.ofFn r,List.ofFn c)).All (FeasibleOutcome r c) := by
  rw [ExactGatePrefix.experiment,Experiment.all_bind]
  apply (Experiment.all_true _).mono
  intro rare _
  cases rare with
  | false =>
    rw [ite_eq_right Bool.false_ne_true,Experiment.all_map]
    exact exactOrdinary_feasible r c htotal
  | true => trivial

lemma print_bound (htotal : (∑ i,r i)=∑ j,c j) (B : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B) :
    (ExactGatePrefix.experiment (List.ofFn r,List.ofFn c)).All
      (fun o => o.elim 0 GreedyFeasibleTable.printMatrixRealizer.cost≤B) := by
  exact (feasible r c htotal).mono (by
    intro o ho
    cases o with
    | none => exact Nat.zero_le _
    | some X => obtain ⟨T,rfl⟩ := ho; exact hB T)

def experiment : Experiment (Option (Table r c)) :=
  (ExactGatePrefix.experiment (List.ofFn r,List.ofFn c)).map (decode r c)

lemma failure (htotal : (∑ i,r i)=∑ j,c j) :
    (experiment r c).mean (fun o => if o=none then 1 else 0)=1/(2:ℚ)^(correctionPrecision r c) := by
  rw [experiment,Experiment.mean_map]
  have he := Experiment.mean_congr_all _
    (fun o => if decode r c o=none then (1:ℚ) else 0)
    (fun o => if o=none then (1:ℚ) else 0)
    ((feasible r c htotal).mono (by
      intro o ho
      simp only [decode_eq_iff r c ho none,code,Option.map_none]))
  rw [he,ExactGatePrefix.failure,exactPrecision_ofFn]

noncomputable def output (o : Option (Table r c)) :
    Cfg Symbol ExactPhysicalProgram.program.State := ExactGatePhysical.output (input r c) (code r c o)

lemma output_injective : Function.Injective (output r c) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some Y =>
      have he := congrArg Cfg.state h
      change (ExactGatePhysical.output (input r c) none).state=
        (ExactGatePhysical.output (input r c) (some (matrixCode Y.val))).state at he
      rw [ExactGatePhysical.output_some] at he
      exact False.elim (ExactGatePhysical.output_none_live _ he)
  | some X =>
    cases b with
    | none =>
      have he := congrArg Cfg.state h
      change (ExactGatePhysical.output (input r c) (some (matrixCode X.val))).state=
        (ExactGatePhysical.output (input r c) none).state at he
      rw [ExactGatePhysical.output_some] at he
      exact False.elim (ExactGatePhysical.output_none_live _ he.symm)
    | some Y =>
      apply congrArg some
      apply PackedMatrixInjective.table_injective X Y
      change ExactGatePhysical.output _ (some (matrixCode X.val))=
        ExactGatePhysical.output _ (some (matrixCode Y.val)) at h
      rw [ExactGatePhysical.output_some,ExactGatePhysical.output_some] at h
      simpa only [Program.final,Cfg.mk.injEq,true_and] using h

theorem table_prefix (htotal : (∑ i,r i)=∑ j,c j) (B : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B) :
    ∃ p,Implements ExactPhysicalProgram.program.table (output r c)
      (ExactPhysicalProgram.program.initial (Tape.mk₁ (TreePost.packed (input r c)))) p ∧
      (∀ g : Option (Table r c) → ℚ,p.mean g=(experiment r c).mean g) ∧
      p.cost≤ExactGatePhysical.budget (input r c) B := by
  have hb : (ExactGatePrefix.experiment (exactParsedMargins (input r c))).All
      (fun o => o.elim 0 GreedyFeasibleTable.printMatrixRealizer.cost≤B) := by
    rw [show exactParsedMargins (input r c)=(List.ofFn r,List.ofFn c) from exactParsedMargins_spec r c]
    exact print_bound r c htotal B hB
  obtain ⟨p,hp,hpm,hpc⟩ := ExactGatePhysical.prefix_correct_cost (input r c) B hb
  have hm (g : Option MatrixCode → ℚ) :
      p.mean g=(ExactGatePrefix.experiment (List.ofFn r,List.ofFn c)).mean g := by
    simpa only [input,exactParsedMargins_spec] using hpm g
  have hall : p.All (FeasibleOutcome r c) := Experiment.all_of_mean_eq hm _ (feasible r c htotal)
  refine ⟨p.map (decode r c),hp.map_all (decode r c) (output r c)
    (hall.mono (by intro o ho; unfold output; rw [code_decode r c ho])),?_,?_⟩
  · intro g
    rw [Experiment.mean_map,hm,experiment,Experiment.mean_map]
  · simpa only [Experiment.cost_map] using hpc

noncomputable def budget (B L : ℕ) : ℕ :=
  LiteralProgram.packTime (input r c).length+ExactGatePhysical.budget (input r c) B+LiteralProgram.postTime L

noncomputable def publicOutput := ExactPublicCost.output r c (output r c)

lemma publicOutput_halted (X : Table r c) : (publicOutput r c (some X)).state=none := rfl

theorem prefix_correct_cost (htotal : (∑ i,r i)=∑ j,c j) (B L : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B)
    (hL : ∀ X : Table r c,(ExactPublicPrefix.word r c X).length≤L) :
    ∃ p,Implements ExactPublicPrefix.program.table (publicOutput r c)
      (ExactPublicPrefix.program.initial (Tape.mk₁ (input r c))) p ∧
      (∀ g : Option (Table r c) → ℚ,p.mean g=(experiment r c).mean g) ∧ p.cost≤budget r c B L := by
  obtain ⟨p,hp,hm,hc⟩ := table_prefix r c htotal B hB
  have hout (X : Table r c) : output r c (some X)=ExactPhysicalProgram.program.final
      (Tape.mk₁ (TreePost.packed (ExactPublicPrefix.word r c X))) := ExactGatePhysical.output_some _ _
  obtain ⟨q,hq,hqm,hqc⟩ := ExactPublicCost.wrap_prefix r c (output r c)
    (output_injective r c) hout L hL p hp
  refine ⟨q,hq,(fun g => (hqm g).trans (hm g)),?_⟩
  exact hqc.trans (by unfold budget; omega)

end
end ContingencyTables.ExactGatePublic

end OAI

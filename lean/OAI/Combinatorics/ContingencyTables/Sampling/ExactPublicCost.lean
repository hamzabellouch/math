import OAI.Combinatorics.ContingencyTables.Sampling.ExactPublicPrefix
import OAI.Combinatorics.ContingencyTables.Sampling.ExactPhysicalCost
import OAI.Combinatorics.ContingencyTables.Sampling.ExactPrintCost

namespace OAI

/-! # Cost-preserving literal wrapping of exact-sampling prefixes -/

namespace ContingencyTables.ExactPublicCost
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms
open scoped Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

def middleOutput (out : Option (Table r c) → Cfg Symbol ExactPhysicalProgram.program.State) :
    Option (Table r c) → Cfg Symbol ExactPublicPrefix.middle.State
  | none => leftCfg LiteralProgram.post.entry (out none)
  | some X => rightCfg (LiteralProgram.post.final (Tape.mk₁ (ExactPublicPrefix.word r c X)))

def output (out : Option (Table r c) → Cfg Symbol ExactPhysicalProgram.program.State)
    (o : Option (Table r c)) : Cfg Symbol ExactPublicPrefix.program.State :=
  rightCfg (middleOutput r c out o)

theorem wrap_prefix (out : Option (Table r c) → Cfg Symbol ExactPhysicalProgram.program.State)
    (hinj : Function.Injective out)
    (hout : ∀ X,out (some X)=ExactPhysicalProgram.program.final
      (Tape.mk₁ (TreePost.packed (ExactPublicPrefix.word r c X))))
    (L : ℕ) (hL : ∀ X,(ExactPublicPrefix.word r c X).length≤L)
    (p : Experiment (Option (Table r c)))
    (hp : Implements ExactPhysicalProgram.program.table out
      (ExactPhysicalProgram.program.initial (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) p) :
    ∃ q,Implements ExactPublicPrefix.program.table (output r c out)
      (ExactPublicPrefix.program.initial (Tape.mk₁ (ExactTablePrefix.input r c))) q ∧
      (∀ g : Option (Table r c) → ℚ,q.mean g=p.mean g) ∧
      q.cost≤LiteralProgram.packTime (ExactTablePrefix.input r c).length+p.cost+LiteralProgram.postTime L := by
  obtain ⟨v,hv,hvm,hvc⟩ := PhysicalPartialSequence.left_prefix_injective
    ExactPhysicalProgram.program.table LiteralProgram.post.table LiteralProgram.post.entry out hinj _ p hp
  have next (o : Option (Table r c)) : ∃ u,
      Implements ExactPublicPrefix.middle.table (middleOutput r c out)
        (leftCfg LiteralProgram.post.entry (out o)) u ∧
      (∀ g : Option (Table r c) → ℚ,u.mean g=g o) ∧ u.cost≤LiteralProgram.postTime L := by
    cases o with
    | none => exact ⟨.done none,.done none,(fun _ => rfl),Nat.zero_le _⟩
    | some X =>
      obtain ⟨u,hu,hum,huc⟩ := LiteralProgram.post_realizes (ExactPublicPrefix.word r c X)
        (ProfilePrograms.printMatrix_alphabet _)
      have hu' := hu.right (M := ExactPhysicalProgram.program.table) LiteralProgram.post.entry
      have hall : u.All (fun T => T=Tape.mk₁ (ExactPublicPrefix.word r c X)) :=
        Experiment.all_of_mean_eq hum _ rfl
      refine ⟨u.map (fun _ => some X),?_,?_,?_⟩
      · have h := hu'.map_all (fun _ => some X) (middleOutput r c out)
          (hall.mono (by intro T hT; rw [hT]; rfl))
        rw [hout]
        simpa only [ExactPublicPrefix.middle,Program.seq,leftCfg,Program.final,Program.initial,
          Option.elim_none,rightCfg,Option.map_some] using h
      · intro g
        rw [Experiment.mean_map,PhysicalPartialSequence.mean_const]
      · rw [Experiment.cost_map]
        exact huc.trans (LiteralProgram.postTime_mono (hL X))
  choose u hu hum huc using next
  let w := v.bind u
  have hw : Implements ExactPublicPrefix.middle.table (middleOutput r c out)
      (ExactPublicPrefix.middle.initial (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) w :=
    hv.bind u _ hu
  have hwm (g : Option (Table r c) → ℚ) : w.mean g=p.mean g := by
    change (v.bind u).mean g=p.mean g
    rw [Experiment.mean_bind]
    simp_rw [hum]
    exact hvm g
  have hwc : w.cost≤p.cost+LiteralProgram.postTime L :=
    (Experiment.cost_bind_le v u _ huc).trans (Nat.add_le_add_right hvc _)
  have hi : ∀ a∈ExactTablePrefix.input r c,a≠0 :=
    GreedyFeasibleTable.encodeMargins_nonzero r c
  obtain ⟨a,ha,ham,hac⟩ := LiteralProgram.pack_realizes (ExactTablePrefix.input r c) hi
  obtain ⟨b,hb,hbm,hbc⟩ := PhysicalPartialSequence.left_prefix LiteralProgram.pack.table
    ExactPublicPrefix.middle.table ExactPublicPrefix.middle.entry LiteralProgram.pack.final _ a ha
  have hall : b.All (fun x => x=LiteralProgram.pack.final
      (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) := by
    rw [Experiment.all_indicator,hbm,ham]
    simp only [Experiment.mean,ite_true]
  have hw' := hw.right (M := LiteralProgram.pack.table) ExactPublicPrefix.middle.entry
  refine ⟨b.bind (fun _ => w),?_,?_,?_⟩
  · apply hb.bind_all (fun _ => w) (output r c out)
    exact hall.mono (by intro x hx; rw [hx]; exact hw')
  · intro g
    rw [Experiment.mean_bind,PhysicalPartialSequence.mean_const]
    exact hwm g
  · have h := Experiment.cost_bind_le b (fun _ => w) w.cost (fun _ => le_rfl)
    omega

/-- Table decoding preserves the finite-prefix work bound. -/
theorem table_prefix (htotal : (∑ i,r i)=∑ j,c j) (N B : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B) :
    ∃ p,Implements ExactPhysicalProgram.program.table (ExactTablePrefix.output r c)
      (ExactPhysicalProgram.program.initial (Tape.mk₁ (TreePost.packed (ExactTablePrefix.input r c)))) p ∧
      (∀ g : Option (Table r c) → ℚ,p.mean g=(ExactTablePrefix.experiment r c N).mean g) ∧
      p.cost≤ExactPhysicalCost.budget (ExactTablePrefix.input r c) N B := by
  have hprint : (ExactCoreProgram.prefixExperiment
      (ProfilePrograms.exactParsedMargins (ExactTablePrefix.input r c)) N).All
      (fun o => o.elim 0 GreedyFeasibleTable.printMatrixRealizer.cost≤B) := by
    rw [show ProfilePrograms.exactParsedMargins (ExactTablePrefix.input r c)=
      (List.ofFn r,List.ofFn c) from SmallGraphProfiles.exactParsedMargins_spec r c]
    exact ExactPrintCost.prefix_print_bound r c htotal B hB N
  obtain ⟨p,hp,hpm,hpc⟩ := ExactPhysicalCost.prefix_correct_cost (ExactTablePrefix.input r c) N B hprint
  have hm (g : Option MatrixCode → ℚ) :
      p.mean g=(ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).mean g := by
    simpa only [ExactTablePrefix.input,SmallGraphProfiles.exactParsedMargins_spec] using hpm g
  have hall : p.All (SmallGraphProfiles.FeasibleOutcome r c) :=
    Experiment.all_of_mean_eq hm _ (SmallGraphProfiles.exactPrefix_feasible r c htotal N)
  refine ⟨p.map (ExactTablePrefix.decode r c),hp.map_all (ExactTablePrefix.decode r c)
    (ExactTablePrefix.output r c) (hall.mono (by
      intro o ho
      unfold ExactTablePrefix.output
      rw [ExactTablePrefix.code_decode r c ho])),?_,?_⟩
  · intro g
    rw [Experiment.mean_map,hm,ExactTablePrefix.experiment,Experiment.mean_map]
  · simpa only [Experiment.cost_map] using hpc

noncomputable def budget (N B L : ℕ) : ℕ :=
  LiteralProgram.packTime (ExactTablePrefix.input r c).length+
    ExactPhysicalCost.budget (ExactTablePrefix.input r c) N B+LiteralProgram.postTime L

theorem prefix_correct_cost (htotal : (∑ i,r i)=∑ j,c j) (N B L : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B)
    (hL : ∀ X : Table r c,(ExactPublicPrefix.word r c X).length≤L) :
    ∃ p,Implements ExactPublicPrefix.program.table (ExactPublicPrefix.output r c)
      (ExactPublicPrefix.program.initial (Tape.mk₁ (ExactTablePrefix.input r c))) p ∧
      (∀ g : Option (Table r c) → ℚ,p.mean g=(ExactTablePrefix.experiment r c N).mean g) ∧
      p.cost≤budget r c N B L := by
  obtain ⟨p,hp,hm,hc⟩ := table_prefix r c htotal N B hB
  have hout (X : Table r c) : ExactTablePrefix.output r c (some X)=
      ExactPhysicalProgram.program.final
        (Tape.mk₁ (TreePost.packed (ExactPublicPrefix.word r c X))) := by
    exact ExactPhysicalProgram.output_some _ _
  obtain ⟨q,hq,hqm,hqc⟩ := wrap_prefix r c (ExactTablePrefix.output r c)
    (ExactTablePrefix.output_injective r c) hout L hL p hp
  refine ⟨q,hq,(fun g => (hqm g).trans (hm g)),?_⟩
  exact hqc.trans (by unfold budget; omega)

lemma quadratic_budget (N B L : ℕ) :
    budget r c N B L≤budget r c 1 B L*(N+1)^2 := by
  have hp := ExactPhysicalCost.quadratic_budget (ExactTablePrefix.input r c) N B
  have hsq : 1≤(N+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hc := Nat.mul_le_mul_left (LiteralProgram.packTime (ExactTablePrefix.input r c).length+
    LiteralProgram.postTime L) hsq
  unfold budget
  nlinarith

end
end ContingencyTables.ExactPublicCost

end OAI

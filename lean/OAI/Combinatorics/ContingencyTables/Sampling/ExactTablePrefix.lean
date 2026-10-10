import OAI.Combinatorics.ContingencyTables.Sampling.ExactPhysicalProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ExactPrefixFeasibility
import OAI.Combinatorics.ContingencyTables.Machines.PackedMatrixInjective

namespace OAI

/-! # Finite physical prefixes indexed by feasible tables -/

namespace ContingencyTables.ExactTablePrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open DensePrograms SmallGraphProfiles Turing
open scoped Classical BigOperators
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)
attribute [local irreducible] ExactCoreProgram.prefixExperiment
  ExactPhysicalProgram.program ExactPhysicalProgram.output

def code (o : Option (Table r c)) : Option MatrixCode := o.map (fun X => matrixCode X.val)

lemma code_injective : Function.Injective (code r c) := by
  intro X Y h
  cases X with
  | none => cases Y <;> simp_all [code]
  | some X =>
    cases Y with
    | none => simp [code] at h
    | some Y =>
      apply congrArg some
      apply Subtype.ext
      have he : matrixCode X.val=matrixCode Y.val := Option.some.inj h
      change List.ofFn (fun i => List.ofFn (X.val i))=List.ofFn (fun i => List.ofFn (Y.val i)) at he
      funext i
      exact List.ofFn_injective (congrFun (List.ofFn_injective he) i)

def decode : Option MatrixCode → Option (Table r c) := Function.invFun (code r c)

lemma decode_code (o : Option (Table r c)) : decode r c (code r c o)=o :=
  Function.leftInverse_invFun (code_injective r c) o

lemma code_decode {o : Option MatrixCode} (h : FeasibleOutcome r c o) :
    code r c (decode r c o)=o := by
  cases o with
  | none => exact congrArg (code r c) (decode_code r c none)
  | some X =>
    obtain ⟨T,hT⟩ := h
    subst X
    exact congrArg (code r c) (decode_code r c (some T))

def experiment (N : ℕ) : Experiment (Option (Table r c)) :=
  (ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).map (decode r c)

lemma decode_eq_iff {o : Option MatrixCode} (ho : FeasibleOutcome r c o)
    (T : Option (Table r c)) : decode r c o=T ↔ o=code r c T := by
  constructor
  · intro h
    exact (code_decode r c ho).symm.trans (congrArg (code r c) h)
  · intro h
    rw [h,decode_code]

lemma event_mean (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) (T : Option (Table r c)) :
    (experiment r c N).mean (fun o => if o=T then 1 else 0)=
      (ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).mean
        (fun o => if o=code r c T then 1 else 0) := by
  rw [experiment,Experiment.mean_map]
  apply Experiment.mean_congr_all
  exact (exactPrefix_feasible r c htotal N).mono (by
    intro o ho
    simp only [decode_eq_iff r c ho T])

lemma failure_bound
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler
      (largeTailCount r (d^20)*largeTailCount c (d^20)))
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid
      (I := Fin (largeTailCount r (d^20)*largeTailCount c (d^20))) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    (experiment r c N).mean (fun o => if o=none then 1 else 0)≤
      (1/(2:ℚ)^(correctionPrecision r c))*(1/2:ℚ)^N := by
  rw [event_mean r c htotal]
  exact exactPrefix_failure r c hPL hCheeger htotal N

lemma point_limit
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler
      (largeTailCount r (d^20)*largeTailCount c (d^20)))
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid
      (I := Fin (largeTailCount r (d^20)*largeTailCount c (d^20))) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (X : Table r c) :
    Filter.Tendsto (fun N => ((experiment r c N).mean
      (fun o => if o=some X then 1 else 0):ℝ)) Filter.atTop
      (nhds ((Fintype.card (Table r c):ℝ)⁻¹)) := by
  have he : (fun N => ((experiment r c N).mean (fun o => if o=some X then 1 else 0):ℝ))=
      (fun N => ((ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).mean
        (fun o => if o=some (matrixCode X.val) then 1 else 0):ℝ)) := by
    funext N
    exact congrArg (fun x : ℚ => (x:ℝ)) (event_mean r c htotal N (some X))
  rw [he]
  exact exactPrefix_limit r c hPL hCheeger htotal X

def input : List Symbol := Algorithms.encodeMargins r c

def output (o : Option (Table r c)) : Cfg Symbol ExactPhysicalProgram.program.State :=
  ExactPhysicalProgram.output (input r c) (code r c o)

lemma output_injective : Function.Injective (output r c) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some Y =>
      have he := congrArg Cfg.state h
      change (ExactPhysicalProgram.output (input r c) none).state=
        (ExactPhysicalProgram.output (input r c) (some (matrixCode Y.val))).state at he
      rw [ExactPhysicalProgram.output_some] at he
      exact False.elim (ExactPhysicalProgram.output_none_live _ he)
  | some X =>
    cases b with
    | none =>
      have he := congrArg Cfg.state h
      change (ExactPhysicalProgram.output (input r c) (some (matrixCode X.val))).state=
        (ExactPhysicalProgram.output (input r c) none).state at he
      rw [ExactPhysicalProgram.output_some] at he
      exact False.elim (ExactPhysicalProgram.output_none_live _ he.symm)
    | some Y =>
      apply congrArg some
      apply PackedMatrixInjective.table_injective X Y
      change ExactPhysicalProgram.output _ (some (matrixCode X.val))=
        ExactPhysicalProgram.output _ (some (matrixCode Y.val)) at h
      rw [ExactPhysicalProgram.output_some,ExactPhysicalProgram.output_some] at h
      simpa only [Program.final,Cfg.mk.injEq,true_and] using h

theorem physical_prefix (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    ∃ p,Implements ExactPhysicalProgram.program.table (output r c)
      (ExactPhysicalProgram.program.initial (Tape.mk₁ (TreePost.packed (input r c)))) p ∧
      ∀ g : Option (Table r c) → ℚ,p.mean g=(experiment r c N).mean g := by
  obtain ⟨p,hp,hpm⟩ := ExactPhysicalProgram.prefix_correct (input r c) N
  have hm (g : Option MatrixCode → ℚ) :
      p.mean g=(ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).mean g := by
    simpa only [input,exactParsedMargins_spec] using hpm g
  have hall : p.All (FeasibleOutcome r c) :=
    Experiment.all_of_mean_eq hm _ (exactPrefix_feasible r c htotal N)
  refine ⟨p.map (decode r c),hp.map_all (decode r c) (output r c)
    (hall.mono (by intro o ho; unfold output; rw [code_decode r c ho])),?_⟩
  intro g
  rw [Experiment.mean_map,hm,experiment,Experiment.mean_map]

end
end ContingencyTables.ExactTablePrefix

end OAI

import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineInitialLaw
import OAI.Combinatorics.MatchingCount.Tapes.Input
import OAI.Combinatorics.MatchingCount.Sampling.Endpoints2
import OAI.Combinatorics.MatchingCount.Machines.OnlineCase
import OAI.Combinatorics.MatchingCount.Graphs.OnlineGraphInvariant

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial

def empty (x : Parsed) : Bool := decide (x.1=0)
def emptyRealizer : Realizer empty := composition (pair first (constant 0)) natEqual
lemma polynomial_empty : PolynomialTime emptyRealizer := by
  exact polynomial_composition (polynomial_pair polynomial_first (polynomial_constant 0)) polynomial_natEqual

def invalid (x : Parsed) : Bool := !(decide (x.1%2=0)) || ExecutableInput.tooSparse (x.1,x.2.1)
def invalidRealizer : Realizer invalid :=
  (choose (composition first ExecutableSource.evenTest)
    (composition (pair first second.fst) ExecutableInput.tooSparseRealizer) (constant true)).congr (by
      intro x
      unfold invalid
      cases h : decide (x.1%2=0) <;> simp only [Function.comp_apply,h,Bool.not_true,Bool.not_false,Bool.false_or,Bool.true_or,Bool.false_eq_true,ite_false,ite_true])
lemma polynomial_invalid : PolynomialTime invalidRealizer := by
  unfold invalidRealizer Realizer.fst
  apply polynomial_congr
  have := ExecutableSource.polynomial_evenTest
  have := ExecutableInput.polynomial_tooSparse
  tree_cost

def materialize (x : Parsed) : OnlineInitial.Seed := ((List.range x.1,x.2.1),x.2.2)
def materializeRealizer : Realizer materialize :=
  pair (pair (composition first range) second.fst) second.snd
lemma work_materialize : WorkBound materializeRealizer (fun x=>x.1+weight x) := by
  have lift {A : Type} [Codec A] {f : Parsed→A} {F : Realizer f} (hF : PolynomialTime F) :
      WorkBound F (fun x=>x.1+weight x) := work_of_polynomial hF X (by intro x;simp)
  unfold materializeRealizer Realizer.fst Realizer.snd
  apply work_pair _ (lift (by tree_cost)) X (by intro x;simp)
  apply work_pair _ (lift (by tree_cost)) X (by intro x;simp)
  apply work_composition (lift polynomial_first) range_numeric_work X
  intro x;simp

def compute (x : Parsed) : Experiment Fraction :=
  OnlineAmplification.run (OnlineInitial.initializeInput (materialize x))
noncomputable def computeRealizer : OnlineTree.Realizer compute :=
  (OnlineTree.composition (OnlineTree.deterministic
    (composition materializeRealizer OnlineInitial.initializeInputRealizer)) OnlineAmplification.runRealizer).congr (fun _ _=>rfl)

def count (x : Parsed) : Experiment Fraction :=
  if empty x then .done (1,1) else if invalid x then .done (0,1) else compute x
noncomputable def countRealizer : OnlineTree.Realizer count :=
  (OnlineTree.conditional emptyRealizer (OnlineTree.deterministic (constant (1,1)))
    (OnlineTree.conditional invalidRealizer (OnlineTree.deterministic (constant (0,1))) computeRealizer)).congr (fun _ _=>rfl)

def algorithm (as : List Symbol) : Experiment (List Symbol) :=
  (count (parseInput as)).map LiteralCodec.ratWord
noncomputable def algorithmRealizer : OnlineTree.Realizer algorithm :=
  (OnlineTree.composition (OnlineTree.composition (OnlineTree.deterministic parseInputRealizer) countRealizer)
    (OnlineTree.deterministic LiteralCodec.ratWordRealizer)).congr (by
      intro as h;simp only [algorithm,Experiment.mean_bind,Experiment.mean,Experiment.mean_map])

lemma edgeNumbers_length (G : GraphInput) : (edgeNumbers G).length=G.edges.card := by
  simp only [edgeNumbers,List.length_map,Finset.length_sort,Finset.card_map]
lemma edgeNumbers_mem (G : GraphInput) (e : ℕ×ℕ) :
    e∈edgeNumbers G ↔ e∈(ExecutableAdaptive.graphRep G).2 := by
  classical
  simp only [edgeNumbers,ExecutableAdaptive.graphRep,List.mem_map,Finset.mem_sort,
    Finset.mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨a,⟨b,hb,rfl⟩,he⟩
    exact ⟨b,hb,he⟩
  · rintro ⟨b,hb,he⟩
    exact ⟨toLex b,⟨b,hb,rfl⟩,he⟩
noncomputable def reorder (G : GraphInput) (es : OnlineGraph.Edges) : OnlineGraph.Edges :=
  if es=(ExecutableAdaptive.graphRep G).2 then edgeNumbers G else es
lemma reorder_mem (G : GraphInput) (es : OnlineGraph.Edges) (e : ℕ×ℕ) :
    e∈reorder G es ↔ e∈es := by
  classical
  unfold reorder
  split
  · rename_i he;rw [he];exact edgeNumbers_mem G e
  · rfl
lemma materialize_source (G : GraphInput) (ε δ : ℚ) :
    materialize (parseInput (encodeInput G ε δ))=
      OnlineGraph.seed (reorder G) (OnlineInitial.sourceSeed (G:=G) ε δ) := by
  rw [parseInput_source]
  unfold materialize OnlineGraph.seed OnlineGraph.graph OnlineInitial.sourceSeed reorder
  simp only [ite_true]
  rfl
lemma compute_mean {G : GraphInput} [Nontrivial (Fin G.n)]
    (hn : 2≤G.n) (hev : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ)
    (h : Fraction→ℚ) :
    (compute (parseInput (encodeInput G ε δ))).mean h=
      PhysicalStream.qaverage (fun b=>h (TreeFraction.repr
        (FiniteTrial.guardedAmplifiedBitOutput (FiniteTrial.parameters G hn hev ε he he1) δ b))) := by
  unfold compute
  rw [materialize_source,OnlineGraph.initialize_mean (reorder G) (reorder_mem G),
    OnlineInitial.initializeInput_source hn hev ε δ he he1 hd]
  exact OnlineAmplification.run_mean _ δ h
end MatchingFPRAS.LiteralAlgorithm

end OAI

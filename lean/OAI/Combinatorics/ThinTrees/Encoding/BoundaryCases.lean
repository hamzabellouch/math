import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.Specification

namespace OAI

/-! Boundary cases. -/

section

namespace AlgorithmicThinTrees
open StrongThinTree Finset

lemma singleton_vertex_cut (n : ℕ) (hn : n = 1) (S : Finset (Fin n))
    (hS : S.Nonempty) : S = univ := by
  subst n
  obtain ⟨v, hv⟩ := hS
  apply eq_univ_of_forall
  intro w
  simpa only [Subsingleton.elim w v] using hv

lemma one_vertex_empty_thinTree {n m : ℕ} (G : MultiGraph n m) (hn : n = 1)
    (C : ℝ) (k : ℕ) : ThinTree C k G ∅ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro S hS hS'
    exact (hS' (singleton_vertex_cut n hn S hS)).elim
  · simp
  · intro S hS hS'
    exact (hS' (singleton_vertex_cut n hn S hS)).elim

lemma one_vertex_tree_unique {n m : ℕ} (G : MultiGraph n m) (hn : n = 1)
    {T : Finset (Fin m)} (hT : G.SpanningTree T) : T = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  apply hT.2 e he
  intro S hS hS'
  exact (hS' (singleton_vertex_cut n hn S hS)).elim

lemma one_vertex_output (C : ℝ) (x : Input) (hn : x.n = 1) :
    GoodOutput C x [] := by
  refine ⟨?_, fun _ => rfl⟩
  cases x with
  | explicit x =>
    refine ⟨[], List.nodup_nil, rfl, ?_⟩
    exact one_vertex_empty_thinTree x.graph hn C x.k
  | binary x =>
    refine ⟨[], List.nodup_nil, rfl, ?_⟩
    simpa [BinaryInput.selected] using one_vertex_empty_thinTree x.graph hn C x.k

def emptyTreeMachine : CurrentKS.Machine where
  stackCount := 2
  states := 1
  initial := 0
  inputStack := 0
  outputStack := 1
  table := []

lemma emptyTreeMachine_run_one (input : List Bool) :
    (emptyTreeMachine.run input 1).state = none ∧
      (emptyTreeMachine.run input 1).stacks emptyTreeMachine.outputStack = [] := by
  simp [CurrentKS.Machine.run, CurrentKS.Machine.step, CurrentKS.Machine.init,
    emptyTreeMachine, CurrentKS.Instruction.halt, CurrentKS.StackAction.apply]

theorem one_vertex_polynomial :
    ∃ M : CurrentKS.Machine, ∃ a degree : ℕ, 0 < a ∧
      ∀ (C : ℝ) (x : Input), x.n = 1 →
        let result := M.run x.encode (a * (x.length + 1) ^ degree)
        result.state = none ∧ GoodOutput C x (result.stacks M.outputStack) := by
  refine ⟨emptyTreeMachine, 1, 0, by decide, ?_⟩
  intro C x hn
  simp only [pow_zero, Nat.mul_one]
  obtain ⟨hhalt, hout⟩ := emptyTreeMachine_run_one x.encode
  exact ⟨hhalt, hout ▸ one_vertex_output C x hn⟩

lemma ExplicitInput.treeOutput_of_thinTree (x : ExplicitInput) {C : ℝ}
    {T : Finset (Fin x.m)} (hT : ThinTree C x.k x.graph T) :
    TreeOutput C (.explicit x) (x.encodeEdges T.toList) := by
  classical
  exact ⟨T.toList, T.nodup_toList, rfl, by simpa using hT⟩

lemma BinaryInput.treeOutput_of_thinTree (x : BinaryInput) {C : ℝ}
    {T : Finset (Fin (Fintype.card x.Edge))} (hT : ThinTree C x.k x.graph T) :
    ∃ bits, TreeOutput C (.binary x) bits := by
  classical
  let F : Finset x.Edge := T.map x.edgeEquiv.symm.toEmbedding
  have hselected : x.selected F.toList = T := by
    ext e
    simp [BinaryInput.selected, F]
  refine ⟨x.encodeEdges F.toList, F.toList, F.nodup_toList, rfl, ?_⟩
  simpa only [hselected] using hT

lemma companion_existence_extension
    (hcomp : ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (n m : ℕ), 2 ≤ n →
      ∀ G : MultiGraph n m, G.EdgeConnected k →
        ∃ T : Finset (Fin m), G.SpanningTree T ∧
          ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
            ((G.cut T S).card : ℝ) ≤ (C / (k : ℝ)) * (G.cut Finset.univ S).card) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Input, Valid x → ∃ bits, GoodOutput C x bits := by
  obtain ⟨C, hC, hcomp⟩ := hcomp
  refine ⟨C, hC, ?_⟩
  intro x hx
  by_cases hn : x.n = 1
  · exact ⟨[], one_vertex_output C x hn⟩
  · have wrap : ∀ bits, TreeOutput C x bits → GoodOutput C x bits :=
      fun bits h => ⟨h, fun h' => (hn h').elim⟩
    cases x with
    | explicit x =>
      obtain ⟨hn', hk, hc⟩ := hx
      have htwo : 2 ≤ x.n := by change x.n ≠ 1 at hn; omega
      obtain ⟨T, htree, hthin⟩ := hcomp x.k hk x.n x.m htwo x.graph hc
      exact ⟨_, wrap _ (x.treeOutput_of_thinTree ⟨htree, hthin⟩)⟩
    | binary x =>
      obtain ⟨hn', hk, hc⟩ := hx
      have htwo : 2 ≤ x.n := by change x.n ≠ 1 at hn; omega
      obtain ⟨T, htree, hthin⟩ :=
        hcomp x.k hk x.n (Fintype.card x.Edge) htwo x.graph hc
      obtain ⟨bits, hb⟩ := x.treeOutput_of_thinTree ⟨htree, hthin⟩
      exact ⟨bits, wrap bits hb⟩

end AlgorithmicThinTrees
end

end OAI

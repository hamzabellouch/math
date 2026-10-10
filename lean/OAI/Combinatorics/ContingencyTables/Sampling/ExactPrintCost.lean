import OAI.Combinatorics.ContingencyTables.Sampling.ExactPrefixFeasibility
import OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicProgram

namespace OAI

/-! # Uniform printing cost for every feasible exact-sampling output -/

namespace ContingencyTables.ExactPrintCost
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open DensePrograms SmallGraphProfiles Polynomial
open scoped BigOperators Classical
noncomputable section

lemma weight_ofFn {A : Type} [Codec A] {n B : ℕ} (f : Fin n → A)
    (h : ∀ i,weight (f i) ≤ B) : weight (List.ofFn f) ≤ n*(B+1)+1 := by
  have hb := weight_map_bound (f := f) (as := List.finRange n) (fun i _ => h i)
  simpa only [←List.ofFn_eq_map,List.length_finRange] using hb

def matrixSize {m n : ℕ} (r : Fin m → ℕ) : ℕ :=
  m*(n*(4*weight (∑ i,r i)+2)+2)+1

lemma matrix_weight {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (X : Table r c) :
    weight (matrixCode X.val) ≤ matrixSize (n := n) r := by
  have row (i : Fin m) : weight (List.ofFn (X.val i)) ≤ n*(4*weight (∑ i,r i)+2)+1 := by
    apply weight_ofFn
    intro j
    exact weight_nat_small (entry_le_total X.property i j)
  exact weight_ofFn (fun i => List.ofFn (X.val i)) row

/-- One fixed polynomial bounds both printing time and printed word length
uniformly over the feasible set. -/
theorem polynomial_print_bound : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (X : Table r c),
      GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)+
        weight (GreedyFeasibleTable.printMatrix (matrixCode X.val)) ≤ p.eval (matrixSize (n := n) r) := by
  obtain ⟨p,hp⟩ := GreedyFeasibleTable.polynomial_printMatrix
  exact ⟨p,fun _ _ r c X => (hp _).trans
    (polynomial_eval_monotone p (matrix_weight r c X))⟩

lemma prefix_print_bound {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (B : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val) ≤ B)
    (N : ℕ) :
    (ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).All
      (fun o => o.elim 0 GreedyFeasibleTable.printMatrixRealizer.cost ≤ B) := by
  exact (exactPrefix_feasible r c htotal N).mono (by
    intro o ho
    cases o with
    | none => exact Nat.zero_le _
    | some X =>
      obtain ⟨T,rfl⟩ := ho
      exact hB T)

end
end ContingencyTables.ExactPrintCost

end OAI

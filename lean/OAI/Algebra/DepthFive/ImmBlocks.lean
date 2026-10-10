import OAI.Algebra.DepthFive.Basic
import OAI.Algebra.DepthFive.MatrixPaths

namespace OAI

noncomputable section

namespace Problem335

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- Each block of layer labels represents the product of its matrices. -/
def immBlock (K : Type*) [CommSemiring K] (n : ℕ) (labels : List (Fin n)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n × Fin n) K) :=
  (labels.map (immLayer K n)).prod

/-- Regrouping consecutive layers does not change the iterated matrix product. -/
theorem imm_eq_blocks_prod (hn : 0 < n) (blocks : List (List (Fin n)))
    (hblocks : blocks.flatten = List.finRange n) :
    imm K n = ((blocks.map (immBlock K n)).prod) ⟨0, hn⟩ ⟨0, hn⟩ := by
  have hm : (blocks.map (fun b : List (Fin n) => b.map (immLayer K n))).flatten =
      (List.finRange n).map (immLayer K n) := by
    rw [← List.map_flatten, hblocks]
  have hp : (blocks.map (immBlock K n)).prod =
      ((List.finRange n).map (immLayer K n)).prod := by
    change (blocks.map (fun b : List (Fin n) => (b.map (immLayer K n)).prod)).prod = _
    simpa only [List.prod_flatten, List.map_map, Function.comp_def] using
      congrArg List.prod hm
  rw [hp]
  simp only [imm, dite_eq_left hn, List.ofFn_eq_map]


/-- The outer path expansion of the block matrices computes `imm`. -/
theorem imm_eq_blocks_path_sum (hn : 0 < n) (blocks : List (List (Fin n)))
    (hblocks : blocks.flatten = List.finRange n) :
    imm K n =
      ((matrixEntryPaths (List.finRange blocks.length) (⟨0, hn⟩ : Fin n) ⟨0, hn⟩).map
        (fun p => (p.map (fun e =>
          immBlock K n (blocks.get e.1) e.2.1 e.2.2)).prod)).sum := by
  rw [matrixEntryPaths_sum_prod (fun j : Fin blocks.length => immBlock K n (blocks.get j))]
  rw [imm_eq_blocks_prod hn blocks hblocks]
  simp [← List.ofFn_eq_map]

end Problem335

end

end OAI

import Mathlib
import OAI.Analysis.AffineBernstein.MatrixMetric

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

omit [Fintype J] in
lemma inverseMatrixPair_sum_left (A : Matrix ι ι ℝ) (t : Finset J)
    (v : J → ι → ℝ) (w : ι → ℝ) :
    inverseMatrixPair A (fun i => ∑ j ∈ t, v j i) w = ∑ j ∈ t, inverseMatrixPair A (v j) w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [inverseMatrixPair]
  | @insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    rw [inverseMatrixPair_add_left,ih]

/- Cauchy--Schwarz for an arbitrary finite linear combination in the literal inverse metric. -/
lemma inverseMatrixPair_combination {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (a : J → ℝ) (v : J → ι → ℝ) :
    inverseMatrixPair A (fun i => ∑ j, a j*v j i) (fun i => ∑ j, a j*v j i) ≤
      (∑ j, a j^2)*(∑ j, inverseMatrixPair A (v j) (v j)) := by
  let z := fun i => ∑ j, a j*v j i
  let B := inverseMatrixPair A z z
  have hB : 0 ≤ B := inverseMatrixPair_self_nonneg hA z
  have hs : B = ∑ j, a j*inverseMatrixPair A (v j) z := by
    dsimp only [B]
    change inverseMatrixPair A (fun i => ∑ j, a j*v j i) z = _
    rw [inverseMatrixPair_sum_left]
    simp only [inverseMatrixPair_smul_left]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := a)
    (g := fun j => inverseMatrixPair A (v j) z)
  have hsum : (∑ j, inverseMatrixPair A (v j) z^2) ≤ (∑ j, inverseMatrixPair A (v j) (v j))*B := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => inverseMatrixPair_cauchy hA (v j) z
  have hn : 0 ≤ ∑ j, a j^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hn
  rw [← hs] at hc
  have hC : 0 ≤ (∑ j, a j^2)*(∑ j, inverseMatrixPair A (v j) (v j)) :=
    mul_nonneg hn (Finset.sum_nonneg fun j _ => inverseMatrixPair_self_nonneg hA (v j))
  change B ≤ _
  nlinarith

end AffineBernstein
end

end OAI

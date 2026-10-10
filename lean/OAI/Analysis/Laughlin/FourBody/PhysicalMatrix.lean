import OAI.Analysis.Laughlin.FourBody.ErrorLimit
import OAI.Analysis.Laughlin.FourBody.SignedCoordinates

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def fourBodyTermMatrix (Q t : ℕ) (e f : ℕ × ℕ × ℤ) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q) (Fin (2*Q-2+1) × WedgePairIndex Q) ℝ :=
  -(sourceAlpha t e * sourceAlpha t f) •
    realOuter (fourSignedUnit Q e.1 e.2.1 (f.1+f.2.1-t))
      (fourSignedUnit Q f.1 f.2.1 (e.1+e.2.1-t))

noncomputable def physicalFourBodyMatrix (Q : ℕ) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q) (Fin (2*Q-2+1) × WedgePairIndex Q) ℝ :=
  (Certificate.rows.map (fun row => (row.2.2.map (fun e =>
    (row.2.2.map (fun f => fourBodyTermMatrix Q row.1 e f)).sum)).sum)).sum

theorem trace_cross_outer {I J : Type*} [Fintype I] [Fintype J]
    (V W : Matrix I J ℝ) (u v : I → ℝ) :
    Matrix.trace (Vᵀ * realOuter u v * W) =
      ∑ n, dotProduct (fun i => V i n) u * dotProduct (fun i => W i n) v := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,realOuter,
    dotProduct,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Laughlin.Spin

end OAI

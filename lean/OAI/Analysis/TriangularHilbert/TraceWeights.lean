import OAI.Analysis.TriangularHilbert.SignedTraceOrder

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma trace_mul_three (X Y Z : Matrix ι ι ℂ) :
    Matrix.trace (X*Y*Z) = ∑ i, ∑ j, ∑ k, X i j*Y j k*Z k i := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

lemma trace_diagonal_triangle (W : Three → Matrix ι ι ℂ) (d : Three → ι → ℝ) :
    Matrix.trace (Matrix.diagonal (fun i => (d 0 i:ℂ))*W 0*
      Matrix.diagonal (fun i => (d 1 i:ℂ))*W 1*
      Matrix.diagonal (fun i => (d 2 i:ℂ))*W 2) =
      ∑ i, ∑ j, ∑ k, ((d 0 i:ℂ)*W 0 i j)*((d 1 j:ℂ)*W 1 j k)*((d 2 k:ℂ)*W 2 k i) := by
  rw [show Matrix.diagonal (fun i => (d 0 i:ℂ))*W 0*
      Matrix.diagonal (fun i => (d 1 i:ℂ))*W 1*
      Matrix.diagonal (fun i => (d 2 i:ℂ))*W 2 =
      (Matrix.diagonal (fun i => (d 0 i:ℂ))*W 0)*
      (Matrix.diagonal (fun i => (d 1 i:ℂ))*W 1)*
      (Matrix.diagonal (fun i => (d 2 i:ℂ))*W 2) by simp only [Matrix.mul_assoc]]
  simp only [trace_mul_three,Matrix.diagonal_mul]

lemma weighted_triangle_entry (a b c : ℂ) (g0 g1 g2 d0 d1 d2 : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) :
    ((d0:ℂ)*((Real.sqrt g0:ℂ)*a*(Real.sqrt g1:ℂ)))*
    ((d1:ℂ)*((Real.sqrt g1:ℂ)*b*(Real.sqrt g2:ℂ)))*
    ((d2:ℂ)*((Real.sqrt g2:ℂ)*c*(Real.sqrt g0:ℂ))) =
      a*b*c*((g0*d0)*(g1*d1)*(g2*d2):ℝ) := by
  have h0 : (Real.sqrt g0:ℂ)^2 = (g0:ℂ) := by exact_mod_cast Real.sq_sqrt hg0
  have h1 : (Real.sqrt g1:ℂ)^2 = (g1:ℂ) := by exact_mod_cast Real.sq_sqrt hg1
  have h2 : (Real.sqrt g2:ℂ)^2 = (g2:ℂ) := by exact_mod_cast Real.sq_sqrt hg2
  calc
    _ = a*b*c*(Real.sqrt g0:ℂ)^2*(Real.sqrt g1:ℂ)^2*(Real.sqrt g2:ℂ)^2*d0*d1*d2 := by ring
    _ = _ := by rw [h0,h1,h2]; push_cast; ring

lemma trace_weighted_triangle (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) :
    Matrix.trace (Matrix.diagonal (fun i => (d 0 i:ℂ))*weightedArray A g 0*
      Matrix.diagonal (fun i => (d 1 i:ℂ))*weightedArray A g 1*
      Matrix.diagonal (fun i => (d 2 i:ℂ))*weightedArray A g 2) =
      ∑ i, ∑ j, ∑ k, A 0 i j*A 1 j k*A 2 k i*((g 0 i*d 0 i)*(g 1 j*d 1 j)*(g 2 k*d 2 k):ℝ) := by
  rw [trace_diagonal_triangle]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact weighted_triangle_entry _ _ _ _ _ _ _ _ _ (hg 0 i) (hg 1 j) (hg 2 k)

end
end TriangularHilbert.MatrixEnergy
end

end OAI

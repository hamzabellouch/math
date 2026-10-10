import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.MatrixProjection
import OAI.Probability.BinarySweep.SparseBounds.CenteredMoment

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexConjugate

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

def centeredMatrix (s : ℝ) (p : Equiv.Perm X → ℂ) : Matrix (I ↪ X) (I ↪ X) ℂ :=
  ∑A ∈ (Finset.univ : Finset I).powerset,
    ((-1:ℂ)^(Fintype.card I-A.card)*(s:ℂ)^A.card/(s:ℂ)^Fintype.card I) •
      ∑g, p g • partialKernel A g

omit [DecidableEq I] in
lemma centeredMatrix_toLin (s : ℝ) (p : Equiv.Perm X → ℂ) :
    (centeredMatrix (I:=I) s p).toEuclideanLin=centeredHilbert s p := by
  simp only [centeredMatrix,map_sum,map_smul,partialKernel_toLin,centeredHilbert_sum]

lemma evenMoment_one_matrix {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J ℂ) : Irrep.evenMoment 1 M.toEuclideanLin = ∑x,∑y, ‖M y x‖^2 := by
  have hc (z : ℂ) : (star z*z).re=‖z‖^2 := by
    rw [Complex.star_def,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]
  unfold Irrep.evenMoment
  rw [pow_one,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,Module.End.mul_eq_comp,← Matrix.toLpLin_mul_same,
    Density.trace_toEuclideanLinear]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact hc (M y x)

theorem specht_moment_one_le_centered_matrix (μ : YoungDiagram) (s : ℝ) (hs : s≠0)
    (p : G μ → ℂ) :
    Irrep.evenMoment 1 (Irrep.groupAverage (hilbertSpecht μ) p) ≤
      ∑x : Tail μ ↪ Cell μ, ∑y, ‖centeredMatrix s p y x‖^2 := by
  have he := centeredHilbert_moment μ s hs p 1
  rw [← centeredMatrix_toLin,evenMoment_one_matrix] at he
  exact he

end BinaryCoordinateSweeps.Young

end

end OAI

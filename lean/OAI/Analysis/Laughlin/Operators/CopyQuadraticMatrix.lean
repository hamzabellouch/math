import OAI.Analysis.Laughlin.Asymptotics.TruncatedMetricPerturbation
import OAI.Analysis.Laughlin.Fock.MatrixQuadratic

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Matrix

noncomputable def copyQuadraticMatrix {I J : Type*} [Fintype I]
    (C : I → I → ℝ) (β : I → J → ℝ) : J → J → ℝ :=
  fun a b => ∑ i, ∑ j, C i j * β i a * β j b

theorem occupationQuadratic_factor {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (C : I → I → ℝ) (β : I → J → ℝ) (v : J → Space Q) :
    occupationQuadratic Q C (fun i => ∑ a, (β i a : ℂ) • v a) =
      occupationQuadratic Q (copyQuadraticMatrix C β) v := by
  let W : Matrix J I ℂ := fun a i => (β i a : ℂ)
  let C' : Matrix I I ℂ := fun i j => (C i j : ℂ)
  have hm (a b : J) : (W*C'*Wᴴ) a b = (copyQuadraticMatrix C β a b : ℂ) := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul]
    simp only [W,C',Complex.star_def,Complex.conj_ofReal,copyQuadraticMatrix,Complex.ofReal_sum,Complex.ofReal_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring
  have h := occupation_matrix_quadratic_factor Q W C' v
  simp only [W,Complex.star_def,Complex.conj_ofReal,hm] at h
  exact congrArg Complex.re h

end Laughlin.Fock

end OAI

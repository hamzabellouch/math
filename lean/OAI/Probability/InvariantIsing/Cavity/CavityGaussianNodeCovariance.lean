import OAI.Probability.InvariantIsing.Cavity.CavityGaussianNodeLaw

namespace OAI

/-! The covariance of a finite linear Gaussian node projection is
positive semidefinite directly from its independent node covariances. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityGaussianNodeCovariance {J : Type*} [Fintype J] {r d : ℕ}
    (S : J → Matrix (Fin d) (Fin d) ℝ) (w : Fin r → J → ℝ) :
    Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ :=
  fun p q => ∑ a, w p.1 a * w q.1 a * S a p.2 q.2

lemma cavityGaussianNodeCovariance_posSemidef {J : Type*} [Fintype J] {r d : ℕ}
    (S : J → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (w : Fin r → J → ℝ) : (cavityGaussianNodeCovariance S w).PosSemidef := by
  classical
  let A : J → Matrix (Fin r × Fin d) (Fin d) ℝ :=
    fun a p j => if p.2 = j then w p.1 a else 0
  have hentry (a : J) (p q : Fin r × Fin d) :
      (A a * S a * (A a).transpose) p q = w p.1 a * w q.1 a * S a p.2 q.2 := by
    change (∑ k : Fin d, (∑ l : Fin d,
      (if p.2 = l then w p.1 a else 0) * S a l k) *
        (if q.2 = k then w q.1 a else 0)) = _
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      mul_ite, mul_zero]
    ring
  have he : cavityGaussianNodeCovariance S w = ∑ a, A a * S a * (A a).transpose := by
    ext p q
    simp only [cavityGaussianNodeCovariance, Matrix.sum_apply, hentry]
  rw [he]
  apply Matrix.posSemidef_sum Finset.univ
  intro a _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hS a).mul_mul_conjTranspose_same (A a)

theorem cavity_gaussian_node_projection_law {J : Type*} [Fintype J] [DecidableEq J]
    {r d : ℕ} (S : J → Matrix (Fin d) (Fin d) ℝ)
    (hS : ∀ a, (S a).PosSemidef) (w : Fin r → J → ℝ) :
    (Measure.pi (fun a => multivariateGaussian 0 (S a))).map
      (cavityGaussianNodeSum w) = multivariateGaussian 0 (cavityGaussianNodeCovariance S w) :=
  cavity_gaussian_node_sum_law S hS w _ (cavityGaussianNodeCovariance_posSemidef S hS w)
    (fun _ _ => rfl)

end InvariantIsing

end

end OAI

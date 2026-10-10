import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem orthonormal_rows_complex_bound {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (c : I → J → ℝ) (v : J → ℂ)
    (hc : ∀ i k, (∑ j, c i j * c k j) = if i = k then 1 else 0) :
    (∑ i, ‖∑ j, (c i j : ℂ) * v j‖^2) ≤ ∑ j, ‖v j‖^2 := by
  let u : I → EuclideanSpace ℂ J := fun i => WithLp.toLp 2 (fun j => (c i j : ℂ))
  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro i k
    simp only [u,PiLp.inner_apply,RCLike.inner_apply,
      Complex.conj_ofReal]
    have h := congrArg Complex.ofReal (hc k i)
    simpa only [Complex.ofReal_sum,Complex.ofReal_mul,
      apply_ite,Complex.ofReal_one,Complex.ofReal_zero,eq_comm] using h
  have h := hu.sum_inner_products_le (WithLp.toLp 2 v) (s := Finset.univ)
  simpa only [u,PiLp.inner_apply,PiLp.toLp_apply,RCLike.inner_apply,
    Complex.star_def,Complex.conj_ofReal,EuclideanSpace.norm_sq_eq,mul_comm] using h

end Laughlin

end OAI

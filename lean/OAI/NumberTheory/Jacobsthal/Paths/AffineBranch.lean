import OAI.NumberTheory.Jacobsthal.Estimates.RegularImplicitArc

namespace OAI

namespace Erdos970

section

namespace ErdosDivisibleInflection

theorem affine_of_second_derivative_zero (f : ℝ → ℝ) (a b x : ℝ)
    (hx : x ∈ Set.Ioo a b) (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (h2 : ∀ t ∈ Set.Ioo a b, deriv (deriv f) t = 0) :
    ∃ A B : ℝ, ∀ t ∈ Set.Ioo a b, f t = A*t+B := by
  have hdf : ContDiffOn ℝ 1 (deriv f) (Set.Ioo a b) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdconst : Set.EqOn (deriv f) (fun _ => deriv f x) (Set.Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (g := fun _ : ℝ => deriv f x) isPreconnected_Ioo
      (hdf.differentiableOn (by norm_num)) (differentiableOn_const (deriv f x)) _ hx rfl
    intro t ht
    simpa only [deriv_const] using h2 t ht
  let A := deriv f x
  let B := f x-A*x
  have hAffine (t : ℝ) : HasDerivAt (fun t => A*t+B) A t := by
    simpa using ((hasDerivAt_id t).const_mul A).add_const B
  have he : Set.EqOn f (fun t => A*t+B) (Set.Ioo a b) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (g := fun t => A*t+B) isPreconnected_Ioo
      (hf.differentiableOn (by norm_num)) (fun t _ => (hAffine t).differentiableAt.differentiableWithinAt)
      _ hx _
    · intro t ht
      rw [(hAffine t).deriv]
      exact hdconst ht
    · dsimp [A,B]
      ring
  exact ⟨A,B,fun t ht => he ht⟩

end ErdosDivisibleInflection

end

end Erdos970

end OAI

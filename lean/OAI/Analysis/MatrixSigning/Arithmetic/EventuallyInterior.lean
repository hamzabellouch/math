import Mathlib
import OAI.Analysis.MatrixSigning.Calculus.JetBound
import OAI.Analysis.MatrixSigning.Arithmetic.Kappa₁

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open Filter CurrentKS.Calculus
open scoped Topology

lemma eventually_interior {x : ℝ} (hx : |x| < 1) : ∀ᶠ y in 𝓝 x, |y| < 1 :=
  IsOpen.eventually_mem (isOpen_lt continuous_abs continuous_const) hx

lemma iteratedDeriv_psi_two {x : ℝ} (hx : |x| < 1) : iteratedDeriv 2 psi x = -kappa x := by
  have he : deriv psi =ᶠ[𝓝 x] psi₁ := by
    filter_upwards [eventually_interior hx] with y hy
    exact (hasDerivAt_psi hy).deriv
  rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
  exact (hasDerivAt_psi₁ hx).deriv

lemma iteratedDeriv_psi_three {x : ℝ} (hx : |x| < 1) : iteratedDeriv 3 psi x = -kappa₁ x := by
  have he : iteratedDeriv 2 psi =ᶠ[𝓝 x] fun y => -kappa y := by
    filter_upwards [eventually_interior hx] with y hy
    exact iteratedDeriv_psi_two hy
  rw [show (3:ℕ)=2+1 from rfl,iteratedDeriv_succ,he.deriv_eq]
  exact (hasDerivAt_kappa hx).neg.deriv

lemma jetBound_psi {σ x : ℝ} (hσ : 0 < σ) (hx : |x| ≤ 1-σ/2) :
    JetBound psi x (1+800/σ^3) := by
  have hi := strip_interior hσ hx
  obtain ⟨h₁,h₂,h₃⟩ := strip_derivative_bounds hσ hx
  have hp : |psi x| ≤ 1 := by rw [abs_of_pos (psi_pos hi)]; exact psi_le_one hi
  have hn : (0:ℝ)≤800/σ^3 := by positivity
  intro n hn'
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  interval_cases n
  · simpa only [iteratedDeriv_zero,Real.norm_eq_abs] using hp.trans (by linarith)
  · rw [iteratedDeriv_one,(hasDerivAt_psi hi).deriv,Real.norm_eq_abs]
    linarith
  · rw [iteratedDeriv_psi_two hi,norm_neg,Real.norm_eq_abs]
    linarith
  · rw [iteratedDeriv_psi_three hi,norm_neg,Real.norm_eq_abs]
    linarith
end
end CurrentKS.Scalar

end OAI

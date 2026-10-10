import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTimeCalculus
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDerivativeBounded

namespace OAI

/-! Exact iterated radial derivatives of the time-symmetry generator. -/

open scoped ContDiff
namespace DefocusingNLS

theorem contDiff_iteratedDeriv_infty {Q : ℝ → ℂ} (hQ : ContDiff ℝ ∞ Q) (N : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv N Q) := by
  induction N with
  | zero => exact hQ
  | succ N ih => rw [iteratedDeriv_succ]; exact ih.deriv'

theorem radialAffineEuler_contDiff (c : ℂ) (Q : ℝ → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    ContDiff ℝ ∞ (radialAffineEuler c Q) := by
  unfold radialAffineEuler
  have hd : ContDiff ℝ ∞ (deriv Q) := hQ.deriv'
  have hr : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)/2) :=
    Complex.ofRealCLM.contDiff.div_const (2 : ℂ)
  exact (contDiff_const.mul hQ).add (hr.mul hd)

theorem radialAffineEuler_iteratedDeriv (c : ℂ) (Q : ℝ → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (N : ℕ) :
    iteratedDeriv N (radialAffineEuler c Q)=
      radialAffineEuler (c+(N : ℂ)/2) (iteratedDeriv N Q) := by
  induction N with
  | zero => simp only [iteratedDeriv_zero,Nat.cast_zero,zero_div,add_zero]
  | succ N ih =>
    rw [iteratedDeriv_succ,ih,radialAffineEuler_deriv _ _ (contDiff_iteratedDeriv_infty hQ N),
      ← iteratedDeriv_succ]
    congr 1
    push_cast
    ring

end DefocusingNLS

end OAI

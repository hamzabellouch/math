import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteBoundedSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIntertwining

namespace OAI

/-! The physical leading frame transforms solutions into the actual root system. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemoteLeadingOperator_eq (c : Fin 2 → ℝ) (t : ℝ) :
    spectralRemoteLeadingOperator c t = (Real.exp t : ℂ)^2 •
      spectralRemoteMatrixOperator (Matrix.diagonal (spectralRemoteDiagonalRoot c)) := by
  rw [← spectralRemoteMatrixOperator_smul,← Matrix.diagonal_smul]
  rfl

theorem spectralRemote_initial_frame_equation
    (c : ℕ → ℝ → Fin 2 → ℝ) (B : ℕ → ℝ → SpectralRemoteOperator) (n : ℕ) (t : ℝ)
    (hc : ∀ i, |c n t i| ≤ 1/32)
    (hP : DifferentiableAt ℝ (fun s => spectralRemoteInitialFrame (c n s)) t) :
    HasDerivAt (fun s => spectralRemoteInitialFrame (c n s))
      (((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading (c n t)+B n t)*
        spectralRemoteInitialFrame (c n t)-spectralRemoteInitialFrame (c n t)*
          (spectralRemoteLeadingOperator (c n t) t+spectralRemoteInitialRemainder c B n t)) t := by
  let P := spectralRemoteInitialFrame (c n t)
  have hu := spectralRemoteInitialFrame_unit (c n t) hc
  have hd := spectralRemoteInitialFrame_diagonalizes (c n t)
    (fun i => (le_abs_self _).trans ((hc i).trans (by norm_num)))
  have hlead : ((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading (c n t))*P =
      P*spectralRemoteLeadingOperator (c n t) t := by
    rw [spectralRemoteLeadingOperator_eq]
    apply ContinuousLinearMap.ext
    intro z
    simp only [mul_apply_eq_comp,smul_apply,map_smul]
    exact congrArg (fun A : SpectralRemoteOperator => (Real.exp t : ℂ)^2 • A z) hd
  have hrem : P*spectralRemoteInitialRemainder c B n t =
      B n t*P-deriv (fun s => spectralRemoteInitialFrame (c n s)) t := by
    exact Ring.mul_inverse_cancel_left _ _ hu
  apply hP.hasDerivAt.congr_deriv
  change _ = (((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading (c n t))+B n t)*P-
    P*(spectralRemoteLeadingOperator (c n t) t+spectralRemoteInitialRemainder c B n t)
  rw [add_mul,mul_add,hlead,hrem]
  abel

theorem spectralRemote_initial_solution
    (c : ℕ → ℝ → Fin 2 → ℝ) (B : ℕ → ℝ → SpectralRemoteOperator)
    (Y : ℝ → SpectralRemoteSpace) (n : ℕ) (t : ℝ)
    (hc : ∀ i, |c n t i| ≤ 1/32)
    (hP : DifferentiableAt ℝ (fun s => spectralRemoteInitialFrame (c n s)) t)
    (hY : HasDerivAt Y
      (((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading (c n t)+B n t) (Y t)) t) :
    HasDerivAt (fun s => Ring.inverse (spectralRemoteInitialFrame (c n s)) (Y s))
      ((spectralRemoteLeadingOperator (c n t) t+spectralRemoteInitialRemainder c B n t)
        (Ring.inverse (spectralRemoteInitialFrame (c n t)) (Y t))) t :=
  spectralRemote_intertwining_solution _ _ _ _ t (spectralRemoteInitialFrame_unit (c n t) hc)
    (spectralRemote_initial_frame_equation c B n t hc hP) hY

end DefocusingNLS

end OAI

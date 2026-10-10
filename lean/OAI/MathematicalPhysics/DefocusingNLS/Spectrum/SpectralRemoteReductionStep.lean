import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Banach
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreen

namespace OAI

/-! One exact near-identity reduction step for the four remote coordinates.
The commutator cancels the off-block coefficient before any norm estimate. -/

namespace DefocusingNLS

abbrev SpectralRemoteSpace := (ℂ × ℂ) × (ℂ × ℂ)
abbrev SpectralRemoteOperator := SpectralRemoteSpace →L[ℂ] SpectralRemoteSpace

theorem spectralRemote_near_identity_inverse (S : SpectralRemoteOperator) (hS : ‖S‖ ≤ 1/2) :
    IsUnit (1+S) ∧ ‖Ring.inverse (1+S)‖ ≤ 2 := by
  have hsmall : ‖-S‖ < 1 := by rw [norm_neg]; linarith
  have hunit : IsUnit (1+S) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hsmall
  have hmul := Ring.inverse_mul_cancel (1+S) hunit
  have hid : Ring.inverse (1+S) = 1-Ring.inverse (1+S)*S := by
    rw [mul_add,mul_one] at hmul
    exact eq_sub_of_add_eq hmul
  have hn : ‖Ring.inverse (1+S)‖ ≤ 1+‖Ring.inverse (1+S)‖*‖S‖ := by
    calc
      _ = ‖1-Ring.inverse (1+S)*S‖ := congrArg norm hid
      _ ≤ ‖(1 : SpectralRemoteOperator)‖+‖Ring.inverse (1+S)*S‖ := norm_sub_le _ _
      _ ≤ 1+‖Ring.inverse (1+S)‖*‖S‖ := by
        rw [norm_one]
        exact add_le_add le_rfl (norm_mul_le (Ring.inverse (1+S)) S)
  have hp := mul_le_mul_of_nonneg_left hS (norm_nonneg (Ring.inverse (1+S)))
  exact ⟨hunit,by linarith⟩

noncomputable def spectralRemoteReducedRemainder
    (L B B₀ S dS : SpectralRemoteOperator) : SpectralRemoteOperator :=
  Ring.inverse (1+S)*((L+B)*(1+S)-dS)-(L+B₀)

theorem spectralRemote_reduction_identity (L B B₀ S dS : SpectralRemoteOperator)
    (hunit : IsUnit (1+S)) (hcomm : L*S-S*L = B₀-B) :
    spectralRemoteReducedRemainder L B B₀ S dS =
      Ring.inverse (1+S)*(B*S-S*B₀-dS) := by
  have he : (L+B)*(1+S)-dS = (1+S)*(L+B₀)+(B*S-S*B₀-dS) := by
    simp only [add_mul,mul_add,one_mul,mul_one]
    rw [eq_add_of_sub_eq hcomm]
    abel
  rw [spectralRemoteReducedRemainder,he,mul_add,Ring.inverse_mul_cancel_left _ _ hunit]
  abel

theorem spectralRemote_reduction_bound (L B B₀ S dS : SpectralRemoteOperator)
    (hS : ‖S‖ ≤ 1/2) (hcomm : L*S-S*L = B₀-B) :
    ‖spectralRemoteReducedRemainder L B B₀ S dS‖ ≤
      2*((‖B‖+‖B₀‖)*‖S‖+‖dS‖) := by
  obtain ⟨hunit,hinv⟩ := spectralRemote_near_identity_inverse S hS
  rw [spectralRemote_reduction_identity L B B₀ S dS hunit hcomm]
  calc
    _ ≤ ‖Ring.inverse (1+S)‖*‖B*S-S*B₀-dS‖ := norm_mul_le _ _
    _ ≤ 2*‖B*S-S*B₀-dS‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ ≤ 2*((‖B‖+‖B₀‖)*‖S‖+‖dS‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _ ≤ ‖B*S-S*B₀‖+‖dS‖ := norm_sub_le _ _
        _ ≤ (‖B*S‖+‖S*B₀‖)+‖dS‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (‖B‖*‖S‖+‖S‖*‖B₀‖)+‖dS‖ :=
          add_le_add (add_le_add (norm_mul_le B S) (norm_mul_le S B₀)) le_rfl
        _ = _ := by ring

end DefocusingNLS

end OAI

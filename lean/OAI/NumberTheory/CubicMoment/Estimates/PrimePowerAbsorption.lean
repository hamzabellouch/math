import OAI.NumberTheory.CubicMoment.Estimates.IdealPrimePowerError
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicMajorant

namespace OAI

/-! The classical higher-prime-power error is absorbed by the same
conductor-uniform exponential majorant at the proved small rate. -/
noncomputable section
namespace CubicFirstMoment

lemma primeCancellation_sqrt_log {c Q X : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1/4)
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X) :
    Real.sqrt X*(Real.log X)^2 ≤ primeCancellationWeight c Q X := by
  have hX1 : 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
    simpa [Real.exp_log hXp] using hh
  have hroot : Real.sqrt X ≤ X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hXp.le,by nlinarith⟩
  have hs := primeDyadic_sqrt_absorption (c := 2*c) (by linarith : 0 ≤ 2*c)
    (by linarith : 2*c ≤ 1/2) hQ hXp hX hroot le_rfl
  rw [show 2*c/2=c by ring] at hs
  have hLP := (primeLogSize_bounds hQ hXp (by linarith)).2.1
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log X) hLP 2
  calc
    _ ≤ (X*Real.exp (-c*Real.log X/primeContourDenominator Q X))*(Real.log (X*Q))^2 :=
      mul_le_mul hs hsq (sq_nonneg _) (by positivity)
    _ = _ := by unfold primeCancellationWeight; ring

theorem idealPrimeChebyshev_bound_of_mangoldt (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {B c Q X : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1/4) (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 2 ≤ Real.log X)
    (hmain : ‖idealMangoldtSum χ X‖ ≤ B*primeCancellationWeight c Q X) :
    ‖idealPrimeChebyshev χ X‖ ≤ (B+idealPrimePowerErrorConstant)*primeCancellationWeight c Q X := by
  have hXe : Real.exp 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show 1 ≤ Real.log X by linarith)
    rwa [Real.exp_log hXp] at hh
  have herr : ‖idealMangoldtSum χ X-idealPrimeChebyshev χ X‖ ≤
      idealPrimePowerErrorConstant*primeCancellationWeight c Q X := by
    calc
      _ ≤ idealPrimePowerErrorConstant*Real.sqrt X*(Real.log X)^2 :=
        idealMangoldt_prime_replacement_log_bound χ hχ hXe
      _ = idealPrimePowerErrorConstant*(Real.sqrt X*(Real.log X)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (primeCancellation_sqrt_log hc hc1 hQ hXp hX)
        idealPrimePowerErrorConstant_pos.le
  calc
    _ = ‖idealMangoldtSum χ X-(idealMangoldtSum χ X-idealPrimeChebyshev χ X)‖ := by
      congr 1
      abel
    _ ≤ ‖idealMangoldtSum χ X‖+‖idealMangoldtSum χ X-idealPrimeChebyshev χ X‖ := norm_sub_le _ _
    _ ≤ B*primeCancellationWeight c Q X+idealPrimePowerErrorConstant*primeCancellationWeight c Q X :=
      add_le_add hmain herr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI

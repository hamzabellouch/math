import OAI.Combinatorics.EditApproximation.Geometry.BandDimension
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalOnlineBand

namespace OAI

/-! The actual guarded band supplies the mass and entropy factors in the node budget. -/

namespace EditApproximation

open Finset

theorem band_dimension_log_of_computed (N : ℕ) (hN : 0 < N) (hell : 42 ≤ inputSmallLog N)
    {nx ny M b P : ℕ} (hMeq : M = (integerParameters N).M) (hPeq : P = (integerParameters N).P)
    (parent : TargetInterval nx) (r : TargetInterval ny) (band : List (Fin M → TargetInterval ny))
    (hband : ∀ action ∈ band, action ∈ wideActionList M parent r b P) :
    Real.log (bandCoordinates band.toFinset).card ≤
      4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ) := by
  subst M P
  exact computed_band_dimension_log N hN hell parent r band hband

theorem unskipped_expected_regret_budget {α : Type*} (source target : List α)
    (N : ℕ) (hN : 0 < N) (hell : 42 ≤ inputSmallLog N) {M b P thetaExponent : ℕ}
    (hMeq : M = (integerParameters N).M) (hPeq : P = (integerParameters N).P)
    (parent : TargetInterval source.length) (tau F : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hF : 0 ≤ F) (c : ℝ) (hb : (b : ℝ) ≤ c)
    (eta kappa delta : ℚ) (heta : 0 < eta) (hkappa : 0 ≤ kappa) (S H : ℕ) :
    ((∑ i, member.envelope i : ℚ) : ℝ) *
        (Real.log (bandCoordinates member.actions.toFinset).card / (eta : ℝ) + 2 * (kappa : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) + 2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c ≤
      (64 * (F : ℝ) *
        ((4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ)) / (eta : ℝ) +
          2 * (kappa : ℝ) + (S : ℝ) / (H : ℝ) ^ 3) +
        2 * (delta : ℝ) + 2 * S * (1 / (H : ℝ) ^ 4) * F) * c := by
  have hlog := band_dimension_log_of_computed N hN hell hMeq hPeq parent member.center member.actions
    (fun action ha => representativeBandActions_wide source target parent member.center b P tau
      ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child action ha)
  have hmass : (0 : ℝ) ≤ ((∑ i, member.envelope i : ℚ) : ℝ) := by
    exact (Rat.cast_nonneg (K := ℝ)).mpr (sum_nonneg fun i _ => (bandChildEnvelope_pos _ _ _ _).le)
  have hmassBound : ((∑ i, member.envelope i : ℚ) : ℝ) ≤ 64 * (F : ℝ) * c := by
    have hQ := (Rat.cast_le (K := ℝ)).mpr member.sum_guard
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] at hQ
    have hFR := (Rat.cast_nonneg (K := ℝ)).mpr hF
    simpa only [UnskippedBand.envelope, UnskippedBand.actions, Rat.cast_sum] using
      hQ.trans (mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num) hFR))
  let upper : ℝ := (4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ)) / (eta : ℝ) +
    2 * (kappa : ℝ) + (S : ℝ) / (H : ℝ) ^ 3
  have hupper : 0 ≤ upper := by
    exact add_nonneg (add_nonneg (div_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      ((Rat.cast_pos (K := ℝ)).mpr heta).le) (mul_nonneg (by norm_num) ((Rat.cast_nonneg (K := ℝ)).mpr hkappa)))
      (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) 3))
  have hbracket : Real.log (bandCoordinates member.actions.toFinset).card / (eta : ℝ) +
      2 * (kappa : ℝ) + (S : ℝ) / (H : ℝ) ^ 3 ≤ upper := by
    dsimp only [upper]
    exact add_le_add_left (add_le_add_left
      (div_le_div_of_nonneg_right hlog ((Rat.cast_pos (K := ℝ)).mpr heta).le) _) _
  have hprod := (mul_le_mul_of_nonneg_left hbracket hmass).trans
    (mul_le_mul_of_nonneg_right hmassBound hupper)
  dsimp only [upper] at hprod
  nlinarith only [hprod]

end EditApproximation

end OAI

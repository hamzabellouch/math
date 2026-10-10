import OAI.Geometry.NodalSets.Elliptic.FirstJetNonvanishing
import OAI.Geometry.NodalSets.Elliptic.RoundCoordinateGradient

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

def roundCorrectionDenominator (u : Yau.Jets.Coord → ℝ) (n : ℕ) : Yau.Jets.Coord → ℝ :=
  Yau.correctionDenominator u (roundCoordGradient u) (seedEigenvalue n)

lemma roundCorrectionDenominator_formula (u : Yau.Jets.Coord → ℝ) (n : ℕ) (x : Yau.Jets.Coord) :
    roundCorrectionDenominator u n x =
      roundCoordFactor x*(sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1)))^2 +
      seedEigenvalue n*(u x)^2 := by
  unfold roundCorrectionDenominator Yau.correctionDenominator
  rw [roundCoordGradient_pairing]

lemma roundCorrectionDenominator_smooth (u : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ContDiff ℝ ∞ (roundCorrectionDenominator u n) :=
  Yau.correctionDenominator_smooth hu
    (fun i ↦ (contDiff_pi.mp (roundCoordGradient_smooth u hu)) i) _

lemma roundCorrectionDenominator_coercive (u : Yau.Jets.Coord → ℝ) {n : ℕ} (hn : 0 < n) (x : Yau.Jets.Coord) :
    ((n:ℝ)^2/2)*(sourceFirstJetSize u n x)^2 ≤ roundCorrectionDenominator u n x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hlam : (n:ℝ)^2 ≤ seedEigenvalue n := by
    unfold seedEigenvalue
    nlinarith
  have h := Yau.first_jet_coercivity (a := |u x|)
    (b := sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1))) hn' hlam
  rw [sq_abs] at h
  have he : sourceFirstJetSize u n x = |u x|+
      sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1))/(n:ℝ) := by
    simp only [sourceFirstJetSize,div_eq_mul_inv,mul_comm]
  rw [he,roundCorrectionDenominator_formula]
  have hp := mul_le_mul_of_nonneg_right (roundCoordFactor_ge_one x)
    (sq_nonneg (sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1))))
  nlinarith

lemma roundCorrectionDenominator_lower (u : Yau.Jets.Coord → ℝ) {n : ℕ} (hn : 0 < n)
    (x : Yau.Jets.Coord) {H : ℝ} (hH : 0 < H)
    (hjet : ((n:ℝ)^65)⁻¹*H ≤ sourceFirstJetSize u n x) :
    (1/2:ℝ)*((n:ℝ)^128)⁻¹*H^2 ≤ roundCorrectionDenominator u n x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hj0 : 0 ≤ ((n:ℝ)^65)⁻¹*H := by positivity
  have hj := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hj0 hjet 2)
    (by positivity : 0 ≤ (n:ℝ)^2/2)
  have he : ((n:ℝ)^2/2)*(((n:ℝ)^65)⁻¹*H)^2 = (1/2:ℝ)*((n:ℝ)^128)⁻¹*H^2 := by
    field_simp
  rw [he] at hj
  exact hj.trans (roundCorrectionDenominator_coercive u hn x)

lemma roundCorrectionDenominator_pos (u : Yau.Jets.Coord → ℝ) {n : ℕ} (hn : 0 < n)
    (x : Yau.Jets.Coord) {H : ℝ} (hH : 0 < H)
    (hjet : ((n:ℝ)^65)⁻¹*H ≤ sourceFirstJetSize u n x) :
    0 < roundCorrectionDenominator u n x :=
  lt_of_lt_of_le (by positivity) (roundCorrectionDenominator_lower u hn x hH hjet)

end
end Yau.Target

end OAI

import OAI.Probability.InvariantIsing.Magnetic.MagneticFourJet
import OAI.Probability.InvariantIsing.Magnetic.MagneticInverseVariation

namespace OAI

/-! Spatial derivatives of q²Hᵤᵤ. Multiplying by q² removes the first-order
term from the differentiated inverse-coordinate continuation equation. -/

noncomputable section

namespace InvariantIsing

def magneticWeightedJetValue (P A : MagneticContinuationFourJet) (z : ℝ) : ℝ :=
  A.second z - A.first z * P.second z / P.first z

def magneticWeightedJetFirst (P A : MagneticContinuationFourJet) (z : ℝ) : ℝ :=
  A.third z - (A.second z * P.second z + A.first z * P.third z) / P.first z +
    A.first z * (P.second z) ^ 2 / (P.first z) ^ 2

def magneticWeightedJetSecond (P A : MagneticContinuationFourJet) (z : ℝ) : ℝ :=
  A.fourth z - A.third z * P.second z / P.first z -
    2 * A.second z * P.third z / P.first z +
    2 * A.second z * (P.second z) ^ 2 / (P.first z) ^ 2 -
    A.first z * P.fourth z / P.first z +
    3 * A.first z * P.second z * P.third z / (P.first z) ^ 2 -
    2 * A.first z * (P.second z) ^ 3 / (P.first z) ^ 3

lemma magneticWeightedJetValue_hasDerivAt (P A : MagneticContinuationFourJet)
    {z : ℝ} (hq : P.first z ≠ 0) :
    HasDerivAt (magneticWeightedJetValue P A) (magneticWeightedJetFirst P A z) z := by
  have hd := (A.dSecond z).sub (((A.dFirst z).mul (P.dSecond z)).div (P.dFirst z) hq)
  convert hd using 1
  · rfl
  · dsimp only [magneticWeightedJetFirst]
    simp only [Pi.mul_apply]
    field_simp [hq]
    ring

lemma magneticWeightedJetFirst_hasDerivAt (P A : MagneticContinuationFourJet)
    {z : ℝ} (hq : P.first z ≠ 0) :
    HasDerivAt (magneticWeightedJetFirst P A) (magneticWeightedJetSecond P A z) z := by
  have hnum := ((A.dSecond z).mul (P.dSecond z)).add ((A.dFirst z).mul (P.dThird z))
  have hlast := ((A.dFirst z).mul ((P.dSecond z).pow 2)).div ((P.dFirst z).pow 2)
    (pow_ne_zero 2 hq)
  have hd := ((A.dThird z).sub (hnum.div (P.dFirst z) hq)).add hlast
  convert hd using 1
  · rfl
  · dsimp only [magneticWeightedJetSecond]
    simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hq]
    ring

def magneticWeightedInverseSecond (P A : MagneticContinuationFourJet) (z : ℝ) : ℝ :=
  magneticWeightedJetSecond P A z / (P.first z) ^ 2 -
    magneticWeightedJetFirst P A z * P.second z / (P.first z) ^ 3

lemma magneticWeightedInverseFirst_hasDerivAt (P A : MagneticContinuationFourJet)
    {b : ℝ → ℝ} {s : ℝ} (hq : P.first (b s) ≠ 0)
    (hb : HasDerivAt b (1 / P.first (b s)) s) :
    HasDerivAt (fun u => magneticWeightedJetFirst P A (b u) / P.first (b u))
      (magneticWeightedInverseSecond P A (b s)) s := by
  exact inverse_mean_pullback_quotient hq hb rfl rfl
    (magneticWeightedJetFirst_hasDerivAt P A hq) (P.dFirst (b s))

lemma magneticWeighted_forward_generator {q r d e x₁ x₂ x₃ x₄ ζ : ℝ}
    (hq : q ≠ 0) :
    ((x₄ / 2 - r * x₃ / (2 * q) + 2 * ζ * q * x₂ + ζ * r * x₁) -
      (x₃ / 2 - r * x₂ / (2 * q) + ζ * q * x₁) * r / q -
      x₁ * (e / 2 - r * d / (2 * q) + 3 * ζ * q * r) / q +
      x₁ * r * (d / 2 - r ^ 2 / (2 * q) + ζ * q ^ 2) / q ^ 2) =
      q ^ 2 / 2 *
        ((x₄ - x₃ * r / q - 2 * x₂ * d / q + 2 * x₂ * r ^ 2 / q ^ 2 -
          x₁ * e / q + 3 * x₁ * r * d / q ^ 2 - 2 * x₁ * r ^ 3 / q ^ 3) / q ^ 2 -
          (x₃ - (x₂ * r + x₁ * d) / q + x₁ * r ^ 2 / q ^ 2) * r / q ^ 3) +
        (d / q - r ^ 2 / q ^ 2 + 2 * ζ * q) * (x₂ - x₁ * r / q) := by
  field_simp [hq]
  ring

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarFourth

namespace OAI

/-! Three spatial derivatives of a bounded continuation through a single
actual Gaussian transition. These are the derivatives needed to close the
inverse-coordinate continuation at the two mean-spin endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def magneticContinuationSecond (ζ : ℝ) (v : ℝ≥0)
    (F M Q A B C : ℝ → ℝ) (z : ℝ) : ℝ :=
  let T := fieldSpinTransition ζ v F
  let D := fieldTiltSpatial ζ v F M
  D B C z + ζ * (D (fun y => A y * M y) (fun y => B y * M y + A y * Q y) z -
    (D A B z * T M z + T A z * D M Q z))

def magneticContinuationThird (ζ : ℝ) (v : ℝ≥0)
    (F M Q R A B C D : ℝ → ℝ) (z : ℝ) : ℝ :=
  let T := fieldSpinTransition ζ v F
  let S := fieldTiltSpatial ζ v F M
  magneticContinuationSecond ζ v F M Q B C D z + ζ *
    (magneticContinuationSecond ζ v F M Q
      (fun y => A y * M y) (fun y => B y * M y + A y * Q y)
      (fun y => C y * M y + 2 * B y * Q y + A y * R y) z -
      (magneticContinuationSecond ζ v F M Q A B C z * T M z +
        2 * S A B z * S M Q z +
        T A z * magneticContinuationSecond ζ v F M Q M Q R z))

lemma hasDerivAt_magneticContinuationSecond (ζ : ℝ) (v : ℝ≥0)
    {F M Q A B C : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    {K L a b c : ℝ} (hK : 0 ≤ K) (_hL : 0 ≤ L) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ L)
    (bA : ∀ y, |A y| ≤ a) (bB : ∀ y, |B y| ≤ b) (bC : ∀ y, |C y| ≤ c)
    (dF : ∀ y, HasDerivAt F (M y) y) (dM : ∀ y, HasDerivAt M (Q y) y)
    (dA : ∀ y, HasDerivAt A (B y) y) (dB : ∀ y, HasDerivAt B (C y) y)
    (z : ℝ) :
    HasDerivAt (fieldTiltSpatial ζ v F M A B)
      (magneticContinuationSecond ζ v F M Q A B C z) z := by
  have bAM : ∀ y, |A y * M y| ≤ a * K := by
    intro y
    rw [abs_mul]
    exact mul_le_mul (bA y) (bM y) (abs_nonneg _) ha
  have bAM' : ∀ y, |B y * M y + A y * Q y| ≤ b * K + a * L := by
    intro y
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (bB y) (bM y) (abs_nonneg _) hb
    · rw [abs_mul]
      exact mul_le_mul (bA y) (bQ y) (abs_nonneg _) ha
  have htA := hasDerivAt_fieldSpinTransition ζ v hF hG hM hA hB hK ha bM bA bB dF dA z
  have htB := hasDerivAt_fieldSpinTransition ζ v hF hG hM hB hC hK hb bM bB bC dF dB z
  have htM := hasDerivAt_fieldSpinTransition ζ v hF hG hM hM hQ hK hK bM bM bQ dF dM z
  have htAM := hasDerivAt_fieldSpinTransition ζ v hF hG hM (hA.mul hM)
    ((hB.mul hM).add (hA.mul hQ)) hK (mul_nonneg ha hK) bM bAM bAM'
    dF (fun y => (dA y).mul (dM y)) z
  exact htB.add ((htAM.sub (htA.mul htM)).const_mul ζ)

lemma hasDerivAt_magneticContinuationThird (ζ : ℝ) (v : ℝ≥0)
    {F M Q R A B C D : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    {K L J a b c d : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ L) (bR : ∀ y, |R y| ≤ J)
    (bA : ∀ y, |A y| ≤ a) (bB : ∀ y, |B y| ≤ b)
    (bC : ∀ y, |C y| ≤ c) (bD : ∀ y, |D y| ≤ d)
    (dF : ∀ y, HasDerivAt F (M y) y) (dM : ∀ y, HasDerivAt M (Q y) y)
    (dQ : ∀ y, HasDerivAt Q (R y) y)
    (dA : ∀ y, HasDerivAt A (B y) y) (dB : ∀ y, HasDerivAt B (C y) y)
    (dC : ∀ y, HasDerivAt C (D y) y) (z : ℝ) :
    HasDerivAt (magneticContinuationSecond ζ v F M Q A B C)
      (magneticContinuationThird ζ v F M Q R A B C D z) z := by
  have bprod {U V : ℝ → ℝ} {u w : ℝ} (hu : 0 ≤ u)
      (bu : ∀ y, |U y| ≤ u) (bv : ∀ y, |V y| ≤ w) (y : ℝ) :
      |U y * V y| ≤ u * w := by
    rw [abs_mul]
    exact mul_le_mul (bu y) (bv y) (abs_nonneg _) hu
  have bAM := bprod ha bA bM
  have bAM' (y : ℝ) : |B y * M y + A y * Q y| ≤ b * K + a * L :=
    (abs_add_le _ _).trans (add_le_add (bprod hb bB bM y) (bprod ha bA bQ y))
  have bAM'' (y : ℝ) : |C y * M y + 2 * B y * Q y + A y * R y| ≤
      c * K + 2 * b * L + a * J := by
    have h2 : |2 * B y * Q y| ≤ 2 * b * L := by
      rw [show 2 * B y * Q y = 2 * (B y * Q y) by ring, abs_mul]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (bprod hb bB bQ y) (by norm_num : (0 : ℝ) ≤ 2)
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (bprod hc bC bM y) h2)) (bprod ha bA bR y))
  have dAM (y : ℝ) : HasDerivAt (fun x => A x * M x)
      (B y * M y + A y * Q y) y := (dA y).mul (dM y)
  have dAM' (y : ℝ) : HasDerivAt (fun x => B x * M x + A x * Q x)
      (C y * M y + 2 * B y * Q y + A y * R y) y := by
    convert ((dB y).mul (dM y)).add ((dA y).mul (dQ y)) using 1
    ring
  have hSA := hasDerivAt_magneticContinuationSecond ζ v hF hG hM hQ hA hB hC
    hK hL ha hb bM bQ bA bB bC dF dM dA dB z
  have hSB := hasDerivAt_magneticContinuationSecond ζ v hF hG hM hQ hB hC hD
    hK hL hb hc bM bQ bB bC bD dF dM dB dC z
  have hSM := hasDerivAt_magneticContinuationSecond ζ v hF hG hM hQ hM hQ hR
    hK hL hK hL bM bQ bM bQ bR dF dM dM dQ z
  have hSAM := hasDerivAt_magneticContinuationSecond ζ v hF hG hM hQ
    (hA.mul hM) ((hB.mul hM).add (hA.mul hQ))
    (((hC.mul hM).add ((measurable_const.mul hB).mul hQ)).add (hA.mul hR))
    hK hL (mul_nonneg ha hK) (by positivity) bM bQ bAM bAM' bAM''
    dF dM dAM dAM' z
  change HasDerivAt (fieldTiltSpatial ζ v F M (fun y => A y * M y)
      (fun y => B y * M y + A y * Q y))
    (magneticContinuationSecond ζ v F M Q (fun y => A y * M y)
      (fun y => B y * M y + A y * Q y)
      (fun y => C y * M y + 2 * B y * Q y + A y * R y) z) z at hSAM
  have hTA : HasDerivAt (fieldSpinTransition ζ v F A)
      (fieldTiltSpatial ζ v F M A B z) z :=
    hasDerivAt_fieldSpinTransition ζ v hF hG hM hA hB hK ha bM bA bB dF dA z
  have hTM : HasDerivAt (fieldSpinTransition ζ v F M)
      (fieldTiltSpatial ζ v F M M Q z) z :=
    hasDerivAt_fieldSpinTransition ζ v hF hG hM hM hQ hK hK bM bM bQ dF dM z
  have hh := hSB.add ((hSAM.sub ((hSA.mul hTM).add (hTA.mul hSM))).const_mul ζ)
  convert hh using 1
  · rfl
  · dsimp only [magneticContinuationThird]
    ring

end InvariantIsing

end

end OAI

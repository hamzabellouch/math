import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMultiplication
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevNonlinearity

namespace OAI

/-! # The actual odd-power map on the expanding-torus norm -/

open scoped ComplexConjugate

namespace DefocusingNLS

theorem expandingFourierCoefficient_conjugate (a k L : ℝ) (f : FourierL2)
    (n : frequencyLattice) :
    expandingFourierCoefficient a k L (fourierConjugate f) n =
      conj (expandingFourierCoefficient a k L f (-n)) := by
  have hw : expandingSobolevWeight a k L (-n) = expandingSobolevWeight a k L n := by
    simp [expandingSobolevWeight, expandingSobolevWeightSq]
  simp only [expandingFourierCoefficient, fourierConjugate_apply, map_mul,
    Complex.conj_ofReal, hw]

theorem expandingTorusFunction_conjugate (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f : FourierL2) (x : SchrodingerTorus) :
    expandingTorusFunction a k L (fourierConjugate f) x =
      conj (expandingTorusFunction a k L f x) := by
  rw [expandingTorusFunction_apply a k L ha ha1 hk hL,
    expandingTorusFunction_apply a k L ha ha1 hk hL, Complex.conj_tsum,
    ← (Equiv.neg frequencyLattice).tsum_eq
      (fun n => expandingFourierCoefficient a k L (fourierConjugate f) n * torusCharacter n x)]
  simp only [Equiv.neg_apply, expandingFourierCoefficient_conjugate, neg_neg,
    torusCharacter_neg, map_mul]

noncomputable def expandingRealBilinearProduct (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    FourierL2 →L[ℝ] FourierL2 →L[ℝ] FourierL2 :=
  (expandingBilinearProduct a k L ha ha1 hk hL).bilinearRestrictScalars ℝ

@[simp] theorem expandingRealBilinearProduct_apply (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2) :
    expandingRealBilinearProduct a k L ha ha1 hk hL f g =
      expandingProduct a k L ha ha1 hk hL f g := rfl

noncomputable def expandingAlgebraBound (a k : ℝ) : ℝ :=
  2 * Real.sqrt (4 ^ k) * expandingEmbeddingBound a k

theorem expandingAlgebraBound_nonneg (a k : ℝ) : 0 ≤ expandingAlgebraBound a k := by
  unfold expandingAlgebraBound expandingEmbeddingBound
  positivity

theorem expandingRealBilinearProduct_norm_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    ‖expandingRealBilinearProduct a k L ha ha1 hk hL‖ ≤ expandingAlgebraBound a k := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (expandingAlgebraBound_nonneg a k)
  intro f g
  exact expandingProduct_norm_le a k L ha ha1 hk hL f g

/-- The Fourier realization of the scalar polynomial `|u|^(2m) u`. -/
noncomputable def expandingOddPower (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    ℕ → FourierL2 → FourierL2
  | 0, f => f
  | m + 1, f => expandingProduct a k L ha ha1 hk hL
      (expandingProduct a k L ha ha1 hk hL
        (expandingOddPower a k L ha ha1 hk hL m f) (fourierConjugate f)) f

theorem expandingOddPower_apply (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (f : FourierL2) (x : SchrodingerTorus) :
    expandingTorusFunction a k L (expandingOddPower a k L ha ha1 hk hL m f) x =
      oddPowerNonlinearity m (expandingTorusFunction a k L f x) := by
  induction m with
  | zero => simp [expandingOddPower, oddPowerNonlinearity]
  | succ m ih =>
    simp only [expandingOddPower, expandingTorusFunction_product a k L ha ha1 hk hL,
      ContinuousMap.mul_apply, expandingTorusFunction_conjugate a k L ha ha1 hk hL, ih]
    simp only [oddPowerNonlinearity, pow_succ, starRingEnd_apply]
    ring

/-- The expanding-torus nonlinearity is smooth as a real Banach-space map. -/
theorem contDiff_expandingOddPower (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) :
    ContDiff ℝ ⊤ (expandingOddPower a k L ha ha1 hk hL m) := by
  induction m with
  | zero => exact contDiff_id
  | succ m ih =>
    have hconj : ContDiff ℝ ⊤ (fourierConjugate : FourierL2 → FourierL2) :=
      sobolevConjugation.contDiff
    exact ((expandingRealBilinearProduct a k L ha ha1 hk hL).contDiff.comp
      (((expandingRealBilinearProduct a k L ha ha1 hk hL).contDiff.comp ih).clm_apply
        hconj)).clm_apply contDiff_id

/-- Polynomial growth has a constant independent of the expanding radius. -/
theorem norm_expandingOddPower_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) (f : FourierL2) :
    ‖expandingOddPower a k L ha ha1 hk hL m f‖ ≤
      expandingAlgebraBound a k ^ (2 * m) * ‖f‖ ^ (2 * m + 1) := by
  let C := expandingAlgebraBound a k
  have hC : 0 ≤ C := expandingAlgebraBound_nonneg a k
  have hprod (u v : FourierL2) :
      ‖expandingProduct a k L ha ha1 hk hL u v‖ ≤ C * ‖u‖ * ‖v‖ :=
    expandingProduct_norm_le a k L ha ha1 hk hL u v
  induction m with
  | zero => simp [expandingOddPower]
  | succ m ih =>
    change ‖expandingProduct a k L ha ha1 hk hL
      (expandingProduct a k L ha ha1 hk hL
        (expandingOddPower a k L ha ha1 hk hL m f) (fourierConjugate f)) f‖ ≤ _
    calc
      _ ≤ C * ‖expandingProduct a k L ha ha1 hk hL
          (expandingOddPower a k L ha ha1 hk hL m f) (fourierConjugate f)‖ * ‖f‖ := hprod _ _
      _ ≤ C * (C * ‖expandingOddPower a k L ha ha1 hk hL m f‖ * ‖f‖) * ‖f‖ := by
        gcongr
        simpa only [fourierConjugate_norm] using
          hprod (expandingOddPower a k L ha ha1 hk hL m f) (fourierConjugate f)
      _ ≤ C * (C * (C ^ (2 * m) * ‖f‖ ^ (2 * m + 1)) * ‖f‖) * ‖f‖ := by gcongr
      _ = _ := by
        change C * (C * (C ^ (2 * m) * ‖f‖ ^ (2 * m + 1)) * ‖f‖) * ‖f‖ =
          C ^ (2 * (m + 1)) * ‖f‖ ^ (2 * (m + 1) + 1)
        simp only [Nat.mul_add, Nat.mul_one, pow_succ]
        ring

end DefocusingNLS

end OAI

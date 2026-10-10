import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevConjugation
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace OAI

/-!
# The odd-power nonlinearity on the Fourier Sobolev space

The convolution product and frequency-reversing conjugation realize the actual
pointwise polynomial `|u|^(2m) u`. The induced map is smooth and locally Lipschitz
on `H^k` whenever `k > 6`.
-/

open scoped ComplexConjugate

namespace DefocusingNLS

/-- Pointwise multiplication viewed as a continuous real-bilinear operation. -/
noncomputable def sobolevRealBilinearProduct (k : ℝ) (hk : 6 < k) :
    FourierL2 →L[ℝ] FourierL2 →L[ℝ] FourierL2 :=
  (sobolevBilinearProduct k hk).bilinearRestrictScalars ℝ

@[simp] theorem sobolevRealBilinearProduct_apply (k : ℝ) (hk : 6 < k)
    (f g : FourierL2) :
    sobolevRealBilinearProduct k hk f g = sobolevProduct k hk f g := rfl

/-- The actual odd-power map on `H^k`, built from its bounded algebra operations. -/
noncomputable def sobolevOddPower (k : ℝ) (hk : 6 < k) : ℕ → FourierL2 → FourierL2
  | 0, f => f
  | m + 1, f => sobolevProduct k hk
      (sobolevProduct k hk (sobolevOddPower k hk m f) (fourierConjugate f)) f

/-- Sobolev odd powers have exactly the claimed pointwise values on the torus. -/
theorem sobolevOddPower_apply (k : ℝ) (hk : 6 < k) (m : ℕ)
    (f : FourierL2) (x : SchrodingerTorus) :
    sobolevTorusFunction k (sobolevOddPower k hk m f) x =
      oddPowerNonlinearity m (sobolevTorusFunction k f x) := by
  induction m with
  | zero => simp [sobolevOddPower, oddPowerNonlinearity]
  | succ m ih =>
    simp only [sobolevOddPower, sobolevTorusFunction_product k hk,
      ContinuousMap.mul_apply, sobolevTorusFunction_conjugate k hk, ih]
    simp only [oddPowerNonlinearity, pow_succ, starRingEnd_apply]
    ring

/-- The Banach-space nonlinearity is smooth as a real map. -/
theorem contDiff_sobolevOddPower (k : ℝ) (hk : 6 < k) (m : ℕ) :
    ContDiff ℝ ⊤ (sobolevOddPower k hk m) := by
  induction m with
  | zero => exact contDiff_id
  | succ m ih =>
    have hconj : ContDiff ℝ ⊤ (fourierConjugate : FourierL2 → FourierL2) :=
      sobolevConjugation.contDiff
    exact ((sobolevRealBilinearProduct k hk).contDiff.comp
      (((sobolevRealBilinearProduct k hk).contDiff.comp ih).clm_apply hconj)).clm_apply
      contDiff_id

/-- Local Lipschitz continuity needed for the semilinear Cauchy problem. -/
theorem locallyLipschitz_sobolevOddPower (k : ℝ) (hk : 6 < k) (m : ℕ) :
    LocallyLipschitz (sobolevOddPower k hk m) :=
  ((contDiff_sobolevOddPower k hk m).of_le (by simp)).locallyLipschitz

/-- The algebra norm controls the polynomial growth of the nonlinearity. -/
theorem norm_sobolevOddPower_le (k : ℝ) (hk : 6 < k) (m : ℕ) (f : FourierL2) :
    ‖sobolevOddPower k hk m f‖ ≤
      ‖sobolevBilinearProduct k hk‖ ^ (2 * m) * ‖f‖ ^ (2 * m + 1) := by
  let C := ‖sobolevBilinearProduct k hk‖
  have hC : 0 ≤ C := norm_nonneg (sobolevBilinearProduct k hk)
  have hprod (u v : FourierL2) : ‖sobolevProduct k hk u v‖ ≤ C * ‖u‖ * ‖v‖ :=
    (sobolevBilinearProduct k hk).le_opNorm₂ u v
  induction m with
  | zero => simp [sobolevOddPower]
  | succ m ih =>
    change ‖sobolevProduct k hk
      (sobolevProduct k hk (sobolevOddPower k hk m f) (fourierConjugate f)) f‖ ≤ _
    calc
      _ ≤ C * ‖sobolevProduct k hk (sobolevOddPower k hk m f) (fourierConjugate f)‖ *
          ‖f‖ := hprod _ _
      _ ≤ C * (C * ‖sobolevOddPower k hk m f‖ * ‖f‖) * ‖f‖ := by
        gcongr
        simpa only [fourierConjugate_norm] using hprod (sobolevOddPower k hk m f)
          (fourierConjugate f)
      _ ≤ C * (C * (C ^ (2 * m) * ‖f‖ ^ (2 * m + 1)) * ‖f‖) * ‖f‖ := by
        gcongr
      _ = _ := by
        change C * (C * (C ^ (2 * m) * ‖f‖ ^ (2 * m + 1)) * ‖f‖) * ‖f‖ =
          C ^ (2 * (m + 1)) * ‖f‖ ^ (2 * (m + 1) + 1)
        simp only [Nat.mul_add, Nat.mul_one, pow_succ]
        ring

end DefocusingNLS

end OAI

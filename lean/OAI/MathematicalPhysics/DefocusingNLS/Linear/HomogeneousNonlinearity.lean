import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousConjugation
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace OAI

/-! # The actual odd-power nonlinearity on the whole-space homogeneous algebra -/

open scoped ComplexConjugate ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousRealProduct (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    HomogeneousY a k →L[ℝ] HomogeneousY a k →L[ℝ] HomogeneousY a k :=
  (homogeneousYProduct a k ha ha1 hk).bilinearRestrictScalars ℝ

noncomputable def homogeneousOddPower (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) : ℕ → HomogeneousY a k → HomogeneousY a k
  | 0, f => f
  | m + 1, f => homogeneousYProduct a k ha ha1 hk
      (homogeneousYProduct a k ha ha1 hk (homogeneousOddPower a k ha ha1 hk m f)
        (homogeneousConjugation a k ha ha1 hk f)) f

theorem homogeneousOddPower_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (f : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousOddPower a k ha ha1 hk m f) y =
      oddPowerNonlinearity m (homogeneousPhysicalCLM a k ha ha1 hk f y) := by
  induction m with
  | zero => simp [homogeneousOddPower, oddPowerNonlinearity]
  | succ m ih =>
    simp only [homogeneousOddPower, homogeneousYProduct_physical,
      homogeneousConjugation_physical, ih, oddPowerNonlinearity, pow_succ, starRingEnd_apply]
    ring

theorem contDiff_homogeneousOddPower (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) :
    ContDiff ℝ ⊤ (homogeneousOddPower a k ha ha1 hk m) := by
  induction m with
  | zero => exact contDiff_id
  | succ m ih =>
    exact ((homogeneousRealProduct a k ha ha1 hk).contDiff.comp
      (((homogeneousRealProduct a k ha ha1 hk).contDiff.comp ih).clm_apply
        (homogeneousConjugation a k ha ha1 hk).contDiff)).clm_apply contDiff_id

theorem locallyLipschitz_homogeneousOddPower (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) :
    LocallyLipschitz (homogeneousOddPower a k ha ha1 hk m) :=
  ((contDiff_homogeneousOddPower a k ha ha1 hk m).of_le (by simp)).locallyLipschitz

theorem norm_homogeneousOddPower_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (f : HomogeneousY a k) :
    ‖homogeneousOddPower a k ha ha1 hk m f‖ ≤
      ‖homogeneousYProduct a k ha ha1 hk‖ ^ (2 * m) * ‖f‖ ^ (2 * m + 1) := by
  let C := ‖homogeneousYProduct a k ha ha1 hk‖
  have hC : 0 ≤ C := norm_nonneg (homogeneousYProduct a k ha ha1 hk)
  have hprod (u v : HomogeneousY a k) :
      ‖homogeneousYProduct a k ha ha1 hk u v‖ ≤ C * ‖u‖ * ‖v‖ :=
    (homogeneousYProduct a k ha ha1 hk).le_opNorm₂ u v
  induction m with
  | zero => simp [homogeneousOddPower]
  | succ m ih =>
    change ‖homogeneousYProduct a k ha ha1 hk
      (homogeneousYProduct a k ha ha1 hk (homogeneousOddPower a k ha ha1 hk m f)
        (homogeneousConjugation a k ha ha1 hk f)) f‖ ≤ _
    calc
      _ ≤ C * ‖homogeneousYProduct a k ha ha1 hk (homogeneousOddPower a k ha ha1 hk m f)
          (homogeneousConjugation a k ha ha1 hk f)‖ * ‖f‖ := hprod _ _
      _ ≤ C * (C * ‖homogeneousOddPower a k ha ha1 hk m f‖ * ‖f‖) * ‖f‖ := by
        gcongr
        simpa only [homogeneousConjugation_norm] using
          hprod (homogeneousOddPower a k ha ha1 hk m f) (homogeneousConjugation a k ha ha1 hk f)
      _ ≤ C * (C * (C ^ (2 * m) * ‖f‖ ^ (2 * m + 1)) * ‖f‖) * ‖f‖ := by gcongr
      _ = _ := by
        change C * (C * (C ^ (2 * m) * ‖f‖ ^ (2 * m + 1)) * ‖f‖) * ‖f‖ =
          C ^ (2 * (m + 1)) * ‖f‖ ^ (2 * (m + 1) + 1)
        simp only [Nat.mul_add, Nat.mul_one, pow_succ]
        ring

end DefocusingNLS

end OAI

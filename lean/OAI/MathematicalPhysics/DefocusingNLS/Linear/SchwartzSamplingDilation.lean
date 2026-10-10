import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingJetBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDilation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingScaleTransfer

namespace OAI

/-! # Exact dilation of the sampled expanding-torus vector

An annulus of physical radius R is sampled at effective period L/R.  The
canonical scale transfer gives exactly the decay factor R^(-a) for 1 ≤ R ≤ L.
-/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem schwartzLatticeCoefficient_homogeneousDilation (a R L : ℝ)
    (hR : 0 < R) (hL : 0 < L) (K : 𝓢(E, ℂ)) (n : frequencyLattice) :
    schwartzLatticeCoefficient L (homogeneousFourierDilation a R hR K) n =
      (R ^ (-2 * a) : ℝ) * schwartzLatticeCoefficient (L / R) K n := by
  have harg : R • (L⁻¹ • (n : E)) = (L / R)⁻¹ • (n : E) := by
    rw [smul_smul]
    congr 1
    field_simp
  have hp : R ^ (12 - 2 * a) = R ^ (12 : ℕ) * R ^ (-2 * a) := by
    calc
      _ = R ^ (12 : ℝ) * R ^ (-2 * a) := by
        rw [← Real.rpow_add hR]
        congr 1
        ring
      _ = _ := by norm_num
  have hc : ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * R ^ (12 - 2 * a) =
      R ^ (-2 * a) * ((2 * Real.pi * (L / R)) ^ (12 : ℕ))⁻¹ := by
    rw [hp]
    field_simp
  simp only [schwartzLatticeCoefficient, homogeneousFourierDilation_apply, harg]
  calc
    _ = (((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ * R ^ (12 - 2 * a) : ℝ) *
        K ((L / R)⁻¹ • (n : E)) := by push_cast; ring
    _ = _ := by rw [hc]; push_cast; ring

theorem schwartzTorusSample_homogeneousDilation (a k R L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (hR : 1 ≤ R) (hRL : R ≤ L) (K : 𝓢(E, ℂ)) :
    schwartzTorusSample a k L ha1 hk (hR.trans hRL)
        (homogeneousFourierDilation a R (by linarith) K) =
      (R ^ (-2 * a) : ℝ) •
        expandingScaleTransfer a k (L / R) L ha hk
          ((le_div_iff₀ (by linarith : 0 < R)).mpr (by simpa using hRL))
          (div_le_self (by linarith : 0 ≤ L) hR)
          (schwartzTorusSample a k (L / R) ha1 hk
            ((le_div_iff₀ (by linarith : 0 < R)).mpr (by simpa using hRL)) K) := by
  have hRp : 0 < R := by linarith
  have hLp : 0 < L := by linarith
  have hLR : 1 ≤ L / R := (le_div_iff₀ hRp).mpr (by simpa using hRL)
  ext n
  change (expandingSobolevWeight a k L n : ℂ) *
      schwartzLatticeCoefficient L (homogeneousFourierDilation a R hRp K) n =
    (R ^ (-2 * a) : ℝ) •
      ((expandingScaleRatio a k (L / R) L n : ℂ) *
        ((expandingSobolevWeight a k (L / R) n : ℂ) *
          schwartzLatticeCoefficient (L / R) K n))
  rw [schwartzLatticeCoefficient_homogeneousDilation a R L hRp hLp]
  simp only [Complex.real_smul, expandingScaleRatio, Complex.ofReal_div]
  have hw : (expandingSobolevWeight a k (L / R) n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k (L / R) hLR n).ne'
  field_simp

theorem schwartzTorusSample_homogeneousDilation_norm_le (a k R L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (hR : 1 ≤ R) (hRL : R ≤ L) (K : 𝓢(E, ℂ)) :
    ‖schwartzTorusSample a k L ha1 hk (hR.trans hRL)
        (homogeneousFourierDilation a R (by linarith) K)‖ ≤
      R ^ (-a) * ‖schwartzTorusSample a k (L / R) ha1 hk
        ((le_div_iff₀ (by linarith : 0 < R)).mpr (by simpa using hRL)) K‖ := by
  have hRp : 0 < R := by linarith
  have hLp : 0 < L := by linarith
  have hLR : 1 ≤ L / R := (le_div_iff₀ hRp).mpr (by simpa using hRL)
  have hratio : L / (L / R) = R := by field_simp
  have hp : R ^ (-2 * a) * R ^ a = R ^ (-a) := by
    rw [← Real.rpow_add hRp]
    congr 1
    ring
  rw [schwartzTorusSample_homogeneousDilation a k R L ha ha1 hk hR hRL,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hRp.le _)]
  calc
    _ ≤ R ^ (-2 * a) * ((L / (L / R)) ^ a *
        ‖schwartzTorusSample a k (L / R) ha1 hk hLR K‖) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hRp.le _)
      exact (expandingScaleTransfer a k (L / R) L ha hk hLR
        (div_le_self hLp.le hR)).le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_right
            (expandingScaleTransfer_norm_le a k (L / R) L ha hk hLR
              (div_le_self hLp.le hR)) (norm_nonneg _))
    _ = _ := by rw [hratio, ← mul_assoc, hp]

end DefocusingNLS

end OAI

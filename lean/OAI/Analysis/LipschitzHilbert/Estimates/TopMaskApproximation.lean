import OAI.Analysis.LipschitzHilbert.Fourier.SincMask
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! The manuscript mask at its actual scale. Inside the prescribed
near region its error is at most a fixed constant times L^(1-A). -/

noncomputable section

namespace LipschitzHilbert

def topSincMask (L A x y : ℝ) : ℝ :=
  sincProductMask ⌈L⌉₊ (x/(L^A)) (y/(L^A))

theorem topSincMask_nonneg (L A x y : ℝ) : 0 ≤ topSincMask L A x y :=
  sincProductMask_nonneg _ _ _

theorem topSincMask_le_one (L A x y : ℝ) : topSincMask L A x y ≤ 1 :=
  sincProductMask_le_one _ _ _

theorem topSincMask_error_le_one (L A x y : ℝ) : |1-topSincMask L A x y| ≤ 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (topSincMask_le_one L A x y))]
  linarith [topSincMask_nonneg L A x y]

theorem abs_one_sub_sincProductMask_scaled (n : ℕ) (T x y : ℝ) (hT : 0 < T)
    (hx : x^2 ≤ T) (hy : y^2 ≤ T) :
    |1-sincProductMask n (x/T) (y/T)| ≤ 2*(n:ℝ)/(3*T) := by
  have hb (z : ℝ) (hz : z^2 ≤ T) : (z/T)^2 ≤ 1/T := by
    rw [div_pow]
    calc
      z^2/T^2 ≤ T/T^2 := div_le_div_of_nonneg_right hz (sq_nonneg T)
      _ = 1/T := by field_simp
  calc
    _ ≤ (n:ℝ)/3*((x/T)^2+(y/T)^2) := abs_one_sub_sincProductMask _ _ _
    _ ≤ (n:ℝ)/3*(1/T+1/T) := mul_le_mul_of_nonneg_left
      (add_le_add (hb x hx) (hb y hy)) (by positivity)
    _ = _ := by ring

theorem topSincMask_near_error (L A x y : ℝ) (hL : 1 ≤ L)
    (hx : |x| ≤ L^(A/2)) (hy : |y| ≤ L^(A/2)) :
    |1-topSincMask L A x y| ≤ (4/3:ℝ)*L^(1-A) := by
  have hL0 : 0 < L := by linarith
  have hT : 0 < L^A := Real.rpow_pos_of_pos hL0 _
  have hpow : (L^(A/2))^2 = L^A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    ring
  have hx2 : x^2 ≤ L^A := by
    rw [← hpow, ← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hy2 : y^2 ≤ L^A := by
    rw [← hpow, ← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hn : (⌈L⌉₊:ℝ) ≤ 2*L := by
    have hc := Nat.ceil_lt_add_one hL0.le
    linarith
  calc
    _ ≤ 2*(⌈L⌉₊:ℝ)/(3*L^A) := abs_one_sub_sincProductMask_scaled _ _ _ _ hT hx2 hy2
    _ ≤ 2*(2*L)/(3*L^A) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = (4/3:ℝ)*L^(1-A) := by rw [Real.rpow_sub hL0, Real.rpow_one]; ring

end LipschitzHilbert

end

end OAI

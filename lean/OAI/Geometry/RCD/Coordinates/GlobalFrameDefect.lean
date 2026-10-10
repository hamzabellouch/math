import OAI.Geometry.RCD.Sobolev.HarmonicGramEnergyDefect

namespace OAI

/-! # A global frame-energy error from the small-defect estimate -/

open Finset
noncomputable section
namespace RegularPointCoordinates

def frameDefectConstant (n : ℕ) : ℝ := 30+5*(1+4*(n:ℝ))^2

theorem frame_energy_defect_global {n : ℕ} {r D : ℝ} (hr : 0≤r) (hD : 0≤D)
    (a : Fin n → ℝ) (ha : ∀ i, (a i)^2≤4*r)
    (hsmall : 5*D≤1 → |r-∑ i, (a i)^2|≤Real.sqrt (30*D)*r) :
    (r-∑ i, (a i)^2)^2≤frameDefectConstant n*D*r^2 := by
  by_cases hgood : 5*D≤1
  · have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hr)).mpr (hsmall hgood)
    rw [sq_abs,mul_pow,Real.sq_sqrt (mul_nonneg (by norm_num) hD)] at hs
    have hc : 30≤frameDefectConstant n := by unfold frameDefectConstant; nlinarith [sq_nonneg (1+4*(n:ℝ))]
    exact hs.trans (by gcongr)
  · have hsum : (∑ i, (a i)^2)≤4*(n:ℝ)*r := by
      calc
        _≤∑ _i : Fin n, 4*r := sum_le_sum (fun i _ => ha i)
        _=_ := by simp; ring
    have hs0 : 0≤∑ i, (a i)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
    have habs : |r-∑ i, (a i)^2|≤(1+4*(n:ℝ))*r := by
      apply abs_le.mpr
      constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) hr)).mpr habs
    rw [sq_abs,mul_pow] at hs
    have hcoef : (1+4*(n:ℝ))^2≤frameDefectConstant n*D := by
      have hd : 1≤5*D := le_of_lt (lt_of_not_ge hgood)
      have hh := mul_le_mul_of_nonneg_right hd (sq_nonneg (1+4*(n:ℝ)))
      unfold frameDefectConstant
      nlinarith
    exact hs.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg r))

end RegularPointCoordinates

end

end OAI

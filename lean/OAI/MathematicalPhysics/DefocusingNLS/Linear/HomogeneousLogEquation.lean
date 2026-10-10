import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogCoefficients

namespace OAI

/-! # Exact logarithmic form of the original physical radial equation -/

open Set Filter Topology

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

theorem homogeneousLogRadialDamping_eq (t : ℝ) :
    homogeneousLogRadialDamping t =
      Real.exp t • homogeneousRadialDamping (Real.exp t) - 1 := by
  have hr : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  have he : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [two_mul, Real.exp_add]
  apply ContinuousLinearMap.ext
  intro w
  apply Prod.ext
  all_goals
    simp only [homogeneousLogRadialDamping, homogeneousLogFastDiagonal,
      homogeneousRadialDamping, spectralTwoColumns_apply, add_apply, sub_apply,
      smul_apply, one_apply_eq_self, ContinuousLinearMap.ofNat_apply,
      Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, Complex.real_smul, smul_eq_mul, nsmul_eq_mul, mul_zero,
      Prod.fst_mul, Prod.snd_mul, Prod.fst_natCast, Prod.snd_natCast,
      add_zero, zero_add, he, Complex.ofReal_mul]
    field_simp [hr]
    ring

theorem homogeneousLogRadialStiffness_eq (νp νm eta : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (t : ℝ) :
    homogeneousLogRadialStiffness νp νm eta m Q t =
      (Real.exp t) ^ 2 • homogeneousRadialStiffness νp νm eta m (Q t) (Real.exp t) := by
  have hr : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  have he : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [two_mul, Real.exp_add]
  apply ContinuousLinearMap.ext
  intro w
  apply Prod.ext
  all_goals
    simp only [homogeneousLogRadialStiffness, homogeneousRadialStiffness,
      spectralTwoColumns_apply, add_apply, smul_apply, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, Complex.real_smul, smul_eq_mul, mul_zero,
      add_zero, zero_add, he, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp [hr]
    ring

theorem homogeneousLogEquation_transform (U W : ℝ → V) (B C : End) (t : ℝ)
    (hU : HasDerivAt U (W (Real.exp t)) (Real.exp t))
    (hW : HasDerivAt W (-B (W (Real.exp t)) - C (U (Real.exp t))) (Real.exp t)) :
    HasDerivAt (fun s => U (Real.exp s)) (Real.exp t • W (Real.exp t)) t ∧
    HasDerivAt (fun s => Real.exp s • W (Real.exp s))
      (-((Real.exp t • B - 1) (Real.exp t • W (Real.exp t))) -
        ((Real.exp t) ^ 2 • C) (U (Real.exp t))) t := by
  refine ⟨hU.scomp t (Real.hasDerivAt_exp t), ?_⟩
  apply ((Real.hasDerivAt_exp t).smul (hW.scomp t (Real.hasDerivAt_exp t))).congr_deriv
  simp only [smul_apply, sub_apply, one_apply_eq_self,
    ContinuousLinearMap.map_smul_of_tower, smul_sub, smul_neg, smul_smul, pow_two]
  abel

theorem homogeneousPhysicalRadial_logEquation (νp νm eta : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (U W : ℝ → V) (t : ℝ)
    (hU : HasDerivAt U (W (Real.exp t)) (Real.exp t))
    (hW : HasDerivAt W
      (-homogeneousRadialDamping (Real.exp t) (W (Real.exp t)) -
        homogeneousRadialStiffness νp νm eta m (Q (Real.exp t)) (Real.exp t)
          (U (Real.exp t))) (Real.exp t)) :
    HasDerivAt (fun s => U (Real.exp s)) (Real.exp t • W (Real.exp t)) t ∧
    HasDerivAt (fun s => Real.exp s • W (Real.exp s))
      (-homogeneousLogRadialDamping t (Real.exp t • W (Real.exp t)) -
        homogeneousLogRadialStiffness νp νm eta m (fun s => Q (Real.exp s)) t
          (U (Real.exp t))) t := by
  rw [homogeneousLogRadialDamping_eq, homogeneousLogRadialStiffness_eq]
  exact homogeneousLogEquation_transform U W _ _ t hU hW

end DefocusingNLS

end OAI

import OAI.Geometry.IsometricImmersion.Energy.MultiplierIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted

def hyperbolicOperator (P S v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (coordPartial 1 v) p -
    P p * coordPartial 0 (coordPartial 1 v) p -
    S p * coordPartial 0 (coordPartial 0 v) p

def energyDensity (S v : Coord → ℝ) (p : Coord) : ℝ :=
  ((coordPartial 1 v p) ^ 2 + S p * (coordPartial 0 v p) ^ 2) / 2

def energyFlux (P S v : Coord → ℝ) (p : Coord) : ℝ :=
  P p * (coordPartial 1 v p) ^ 2 / 2 +
    S p * coordPartial 0 v p * coordPartial 1 v p

def energyCoefficientError (P S bTheta bXi v : Coord → ℝ) (p : Coord) : ℝ :=
  (bTheta p - coordPartial 0 P p / 2) * (coordPartial 1 v p) ^ 2 +
    (bXi p - coordPartial 0 S p) * coordPartial 0 v p * coordPartial 1 v p +
    coordPartial 1 S p / 2 * (coordPartial 0 v p) ^ 2

variable {P S bTheta bXi v R : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem energyDensity_partial_theta
    (hS : DifferentiableAt ℝ S p)
    (hvt : DifferentiableAt ℝ (coordPartial 1 v) p)
    (hvx : DifferentiableAt ℝ (coordPartial 0 v) p) :
    coordPartial 1 (energyDensity S v) p =
      coordPartial 1 v p * coordPartial 1 (coordPartial 1 v) p +
      S p * coordPartial 0 v p * coordPartial 1 (coordPartial 0 v) p +
      coordPartial 1 S p / 2 * (coordPartial 0 v p) ^ 2 := by
  have hd := ((hvt.hasFDerivAt.fun_mul hvt.hasFDerivAt).add
    (hS.hasFDerivAt.fun_mul (hvx.hasFDerivAt.fun_mul hvx.hasFDerivAt))).mul_const
      (1 / 2 : ℝ)
  simp only [Pi.add_def, coordPartial, one_div] at hd
  unfold energyDensity
  simp only [div_eq_mul_inv, pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem energyFlux_partial_xi
    (hP : DifferentiableAt ℝ P p) (hS : DifferentiableAt ℝ S p)
    (hvt : DifferentiableAt ℝ (coordPartial 1 v) p)
    (hvx : DifferentiableAt ℝ (coordPartial 0 v) p) :
    coordPartial 0 (energyFlux P S v) p =
      coordPartial 0 P p / 2 * (coordPartial 1 v p) ^ 2 +
      P p * coordPartial 1 v p * coordPartial 0 (coordPartial 1 v) p +
      coordPartial 0 S p * coordPartial 0 v p * coordPartial 1 v p +
      S p * coordPartial 0 (coordPartial 0 v) p * coordPartial 1 v p +
      S p * coordPartial 0 v p * coordPartial 0 (coordPartial 1 v) p := by
  have hd := ((hP.hasFDerivAt.fun_mul
    (hvt.hasFDerivAt.fun_mul hvt.hasFDerivAt)).mul_const (1 / 2 : ℝ)).add
      ((hS.hasFDerivAt.fun_mul hvx.hasFDerivAt).fun_mul hvt.hasFDerivAt)
  simp only [Pi.add_def, coordPartial, one_div] at hd
  unfold energyFlux
  simp only [div_eq_mul_inv, pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem energy_density_flux_identity
    (hP : DifferentiableAt ℝ P p) (hS : DifferentiableAt ℝ S p)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hp : p ∈ U)
    (hEq : hyperbolicOperator P S v p =
      bTheta p * coordPartial 1 v p + bXi p * coordPartial 0 v p + R p) :
    coordPartial 1 (energyDensity S v) p - coordPartial 0 (energyFlux P S v) p =
      energyCoefficientError P S bTheta bXi v p + R p * coordPartial 1 v p := by
  have hd (i : Fin 2) : DifferentiableAt ℝ (coordPartial i v) p :=
    ((partial_contDiffOn hv hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [energyDensity_partial_theta hS (hd 1) (hd 0),
    energyFlux_partial_xi hP hS (hd 1) (hd 0), coordPartial_comm hv hU hp 1 0]
  unfold hyperbolicOperator at hEq
  unfold energyCoefficientError
  nlinarith [congrArg (fun x : ℝ => x * coordPartial 1 v p) hEq]

theorem energy_fields_contDiffOn
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hS : ContDiffOn ℝ ∞ S U)
    (hbt : ContDiffOn ℝ ∞ bTheta U) (hbx : ContDiffOn ℝ ∞ bXi U)
    (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (energyDensity S v) U ∧
    ContDiffOn ℝ ∞ (energyFlux P S v) U ∧
    ContDiffOn ℝ ∞ (energyCoefficientError P S bTheta bXi v) U := by
  have ht := partial_contDiffOn hv hU 1
  have hx := partial_contDiffOn hv hU 0
  have hPx := partial_contDiffOn hP hU 0
  have hSx := partial_contDiffOn hS hU 0
  have hSt := partial_contDiffOn hS hU 1
  exact ⟨((ht.pow 2).add (hS.mul (hx.pow 2))).div_const 2,
    ((hP.mul (ht.pow 2)).div_const 2).add ((hS.mul hx).mul ht),
    (((hbt.sub (hPx.div_const 2)).mul (ht.pow 2)).add
      (((hbx.sub hSx).mul hx).mul ht)).add ((hSt.div_const 2).mul (hx.pow 2))⟩

theorem energyDensity_nonneg (hS : 0 ≤ S p) : 0 ≤ energyDensity S v p := by
  unfold energyDensity
  positivity

theorem scalar_flux_bound (P S a b : ℝ) (hS : 0 ≤ S) :
    |P * a ^ 2 / 2 + S * b * a| ≤
      (|P| + Real.sqrt S) * ((a ^ 2 + S * b ^ 2) / 2) := by
  have hs := Real.sqrt_nonneg S
  have hs2 := Real.sq_sqrt hS
  have hab : 2 * Real.sqrt S * (|a| * |b|) ≤ a ^ 2 + S * b ^ 2 := by
    nlinarith [sq_nonneg (|a| - Real.sqrt S * |b|), sq_abs a, sq_abs b]
  have hab' := mul_le_mul_of_nonneg_left hab hs
  have hsimpl : Real.sqrt S * (2 * Real.sqrt S * (|a| * |b|)) =
      2 * S * |b| * |a| := by
    calc
      _ = 2 * (Real.sqrt S) ^ 2 * |b| * |a| := by ring
      _ = _ := by rw [hs2]
  rw [hsimpl] at hab'
  have hsa : S * |b| * |a| ≤ Real.sqrt S * ((a ^ 2 + S * b ^ 2) / 2) := by
    nlinarith only [hab']
  calc
    _ ≤ |P * a ^ 2 / 2| + |S * b * a| := abs_add_le _ _
    _ = |P| * a ^ 2 / 2 + S * |b| * |a| := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg a),
        abs_mul, abs_mul, abs_of_nonneg hS]
      norm_num
    _ ≤ |P| * ((a ^ 2 + S * b ^ 2) / 2) +
        Real.sqrt S * ((a ^ 2 + S * b ^ 2) / 2) := by
      have hsb := mul_nonneg (abs_nonneg P) (mul_nonneg hS (sq_nonneg b))
      nlinarith
    _ = _ := by ring

theorem energyFlux_abs_le (hS : 0 ≤ S p) :
    |energyFlux P S v p| ≤ (|P p| + Real.sqrt (S p)) * energyDensity S v p :=
  scalar_flux_bound (P p) (S p) (coordPartial 1 v p) (coordPartial 0 v p) hS

theorem inward_boundary_nonpositive {left right : Coord} {c : ℝ}
    (hSl : 0 ≤ S left) (hSr : 0 ≤ S right)
    (hcl : |P left| + Real.sqrt (S left) ≤ c)
    (hcr : |P right| + Real.sqrt (S right) ≤ c) :
    energyFlux P S v right - energyFlux P S v left -
      c * (energyDensity S v right + energyDensity S v left) ≤ 0 := by
  have hl := (energyFlux_abs_le (P := P) (v := v) hSl).trans
    (mul_le_mul_of_nonneg_right hcl (energyDensity_nonneg (v := v) hSl))
  have hr := (energyFlux_abs_le (P := P) (v := v) hSr).trans
    (mul_le_mul_of_nonneg_right hcr (energyDensity_nonneg (v := v) hSr))
  have hll := (abs_le.mp hl).1
  have hrr := (abs_le.mp hr).2
  linarith

theorem scalar_coefficient_error_bound
    {s0 S M bt bx Px Sx St a b : ℝ} (hs0 : 0 < s0) (hS : s0 ≤ S)
    (hM : 0 ≤ M) (hbt : |bt| ≤ M) (hbx : |bx| ≤ M)
    (hPx : |Px| ≤ M) (hSx : |Sx| ≤ M) (hSt : |St| ≤ M) :
    |(bt - Px / 2) * a ^ 2 + (bx - Sx) * b * a + St / 2 * b ^ 2| ≤
      (8 * M * (1 + 1 / s0)) * ((a ^ 2 + S * b ^ 2) / 2) := by
  have hA : |bt - Px / 2| ≤ 2 * M := by
    have hh := abs_sub bt (Px / 2)
    rw [abs_div] at hh
    norm_num at hh
    linarith
  have hB : |bx - Sx| ≤ 2 * M := (abs_sub _ _).trans (by linarith)
  have hC : |St / 2| ≤ M := by rw [abs_div]; norm_num; linarith
  have hab : |b| * |a| ≤ (a ^ 2 + b ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hrough :
      |(bt - Px / 2) * a ^ 2 + (bx - Sx) * b * a + St / 2 * b ^ 2| ≤
        4 * M * (a ^ 2 + b ^ 2) := by
    calc
      _ ≤ |(bt - Px / 2) * a ^ 2| + |(bx - Sx) * b * a| + |St / 2 * b ^ 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |bt - Px / 2| * a ^ 2 + |bx - Sx| * (|b| * |a|) + |St / 2| * b ^ 2 := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg a), abs_of_nonneg (sq_nonneg b)]
        ring
      _ ≤ (2 * M) * a ^ 2 + (2 * M) * ((a ^ 2 + b ^ 2) / 2) + M * b ^ 2 := by
        gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hM (sq_nonneg a), mul_nonneg hM (sq_nonneg b)]
  have hinv : 0 < 1 / s0 := one_div_pos.mpr hs0
  have hsb : b ^ 2 ≤ (1 / s0) * (S * b ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hS (sq_nonneg b)
    have hh' : b ^ 2 ≤ (S * b ^ 2) / s0 :=
      (le_div_iff₀ hs0).2 (by nlinarith)
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh'
  have hcompare : a ^ 2 + b ^ 2 ≤ (1 + 1 / s0) * (a ^ 2 + S * b ^ 2) := by
    nlinarith [mul_nonneg hinv.le (sq_nonneg a), mul_nonneg (hs0.le.trans hS) (sq_nonneg b)]
  exact hrough.trans (by nlinarith [mul_le_mul_of_nonneg_left hcompare (by positivity : 0 ≤ 4 * M)])

theorem energyCoefficientError_abs_le
    {s0 M : ℝ} (hs0 : 0 < s0) (hS : s0 ≤ S p) (hM : 0 ≤ M)
    (hbt : |bTheta p| ≤ M) (hbx : |bXi p| ≤ M)
    (hPx : |coordPartial 0 P p| ≤ M) (hSx : |coordPartial 0 S p| ≤ M)
    (hSt : |coordPartial 1 S p| ≤ M) :
    |energyCoefficientError P S bTheta bXi v p| ≤
      (8 * M * (1 + 1 / s0)) * energyDensity S v p :=
  scalar_coefficient_error_bound hs0 hS hM hbt hbx hPx hSx hSt

end SmoothLocal.Hyperbolic

end

end OAI

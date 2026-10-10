import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicTestCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace OAI

/-! # Real powers of the squared radius away from the origin -/

open Set Filter Topology
open scoped ContDiff Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def physicalRadiusPower (c : ℝ) (x : E) : ℂ :=
  ((‖x‖ ^ 2) ^ c : ℝ)

theorem realPowerComplex_contDiffAt (c s : ℝ) (hs : s ≠ 0) :
    ContDiffAt ℝ ∞ (fun t : ℝ => ((t ^ c : ℝ) : ℂ)) s :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp s (Real.contDiffAt_rpow_const_of_ne hs)

theorem realPowerComplex_deriv (c s : ℝ) (hs : s ≠ 0) :
    deriv (fun t : ℝ => ((t ^ c : ℝ) : ℂ)) s = (c : ℂ) * (s ^ (c - 1) : ℝ) := by
  simpa only [Complex.ofReal_mul] using
    (Real.hasDerivAt_rpow_const (p := c) (Or.inl hs)).ofReal_comp.deriv

theorem realPowerComplex_deriv_two (c s : ℝ) (hs : s ≠ 0) :
    deriv (deriv (fun t : ℝ => ((t ^ c : ℝ) : ℂ))) s =
      (c : ℂ) * ((c - 1 : ℝ) : ℂ) * (s ^ ((c - 1) - 1) : ℝ) := by
  have he : deriv (fun t : ℝ => ((t ^ c : ℝ) : ℂ)) =ᶠ[𝓝 s]
      (fun t : ℝ => (c : ℂ) * (t ^ (c - 1) : ℝ)) := by
    filter_upwards [eventually_ne_nhds hs] with t ht
    exact realPowerComplex_deriv c t ht
  rw [he.deriv_eq]
  simpa only [Complex.ofReal_mul, mul_assoc] using
    ((Real.hasDerivAt_rpow_const (p := c - 1) (Or.inl hs)).ofReal_comp.const_mul
      (c : ℂ)).deriv

theorem physicalRadiusPower_contDiffAt (c : ℝ) (x : E) (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (physicalRadiusPower c) x := by
  change ContDiffAt ℝ ∞ (fun y : E => (((‖y‖ ^ 2) ^ c : ℝ) : ℂ)) x
  have h := (realPowerComplex_contDiffAt c (‖x‖ ^ 2)
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))).comp x (contDiff_norm_sq ℝ).contDiffAt
  simpa only [Function.comp_def] using h

theorem physicalRadiusPower_fderiv (c : ℝ) (x v : E) (hx : x ≠ 0) :
    fderiv ℝ (physicalRadiusPower c) x v =
      2 * (c : ℂ) * (inner ℝ x v : ℂ) / (‖x‖ ^ 2 : ℝ) * physicalRadiusPower c x := by
  have hs : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  change fderiv ℝ (fun y : E => (((‖y‖ ^ 2) ^ c : ℝ) : ℂ)) x v = _
  rw [radialSquareLift_fderiv _ x v
    ((realPowerComplex_contDiffAt c _ hs).differentiableAt (by simp)),
    realPowerComplex_deriv c _ hs, Real.rpow_sub_one hs]
  simp only [physicalRadiusPower, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  ring

theorem physicalRadiusPower_laplacian (c : ℝ) (x : E) (hx : x ≠ 0) :
    Δ (physicalRadiusPower c) x =
      (4 * (c : ℂ) * ((c + 5 : ℝ) : ℂ) / (‖x‖ ^ 2 : ℝ)) *
        physicalRadiusPower c x := by
  have hs : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hsc : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  change Δ (fun y : E => (((‖y‖ ^ 2) ^ c : ℝ) : ℂ)) x = _
  rw [radialSquareLift_laplacian _ x
    ((realPowerComplex_contDiffAt c _ hs).of_le (by simp)),
    realPowerComplex_deriv c _ hs, realPowerComplex_deriv_two c _ hs,
    Real.rpow_sub_one hs (c - 1), Real.rpow_sub_one hs c]
  simp only [physicalRadiusPower, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.ofReal_one,
    Complex.ofReal_pow]
  field_simp [hsc]
  ring

end DefocusingNLS

end OAI

import OAI.Geometry.IsometricImmersion.Calculus.CoordinateDerivatives
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {f h : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem coordPartial_div
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) (i : Fin 2) :
    coordPartial i (fun x => f x / h x) p =
      (coordPartial i f p * h p - f p * coordPartial i h p) / (h p) ^ 2 := by
  have hinv : HasFDerivAt (fun x : Coord => (h x)⁻¹)
      (-(h p ^ 2)⁻¹ • fderiv ℝ h p) p := by
    simpa only [Function.comp_def] using
      (hasDerivAt_inv hne).comp_hasFDerivAt p hh.hasFDerivAt
  have hquot : HasFDerivAt (fun x : Coord => f x / h x)
      (f p • (-(h p ^ 2)⁻¹ • fderiv ℝ h p) +
        (h p)⁻¹ • fderiv ℝ f p) p := by
    simpa only [div_eq_mul_inv] using hf.hasFDerivAt.fun_mul hinv
  unfold coordPartial
  rw [hquot.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp [hne]
  ring

theorem coordPartial_div_on
    (hU : IsOpen U) (hp : p ∈ U)
    (hf : DifferentiableOn ℝ f U) (hh : DifferentiableOn ℝ h U)
    (hne : h p ≠ 0) (i : Fin 2) :
    coordPartial i (fun x => f x / h x) p =
      (coordPartial i f p * h p - f p * coordPartial i h p) / (h p) ^ 2 := by
  exact coordPartial_div (hf.differentiableAt (hU.mem_nhds hp))
    (hh.differentiableAt (hU.mem_nhds hp)) hne i

def coordinateDrift (q w : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 w p - q p * coordPartial 1 w p

theorem coordinateDrift_quotient (q : Coord → ℝ)
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) :
    coordinateDrift q (fun x => f x / h x) p =
      (coordinateDrift q f p * h p - f p * coordinateDrift q h p) / (h p) ^ 2 := by
  unfold coordinateDrift
  rw [coordPartial_div hf hh hne 0, coordPartial_div hf hh hne 1]
  field_simp [hne]
  ring

theorem coordinateDrift_self_quotient
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) :
    coordinateDrift (fun x => f x / h x) (fun x => f x / h x) p =
      (coordPartial 0 f p - (f p / h p) * coordPartial 1 f p) / h p -
        (f p / h p) *
          (coordPartial 0 h p - (f p / h p) * coordPartial 1 h p) / h p := by
  rw [coordinateDrift_quotient (fun x => f x / h x) hf hh hne]
  unfold coordinateDrift
  field_simp [hne]

theorem quotient_contDiffOn
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (hne : ∀ p ∈ U, h p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => f p / h p) U := by
  exact hf.div hh hne

def explicitDriftError (h E T J : Coord → ℝ) (p : Coord) : ℝ :=
  E p / (h p) ^ 2 * (T p - coordPartial 1 h p / h p) + J p / h p

theorem explicitDriftError_contDiffOn
    {E T J : Coord → ℝ} (hU : IsOpen U)
    (hh : ContDiffOn ℝ ∞ h U) (hE : ContDiffOn ℝ ∞ E U)
    (hT : ContDiffOn ℝ ∞ T U) (hJ : ContDiffOn ℝ ∞ J U)
    (hne : ∀ p ∈ U, h p ≠ 0) :
    ContDiffOn ℝ ∞ (explicitDriftError h E T J) U := by
  have hG : ContDiffOn ℝ ∞ (fun p => E p / (h p) ^ 2) U :=
    hE.div (hh.pow 2) (fun p hp => pow_ne_zero 2 (hne p hp))
  have hhy : ContDiffOn ℝ ∞ (coordPartial 1 h) U :=
    partial_contDiffOn hh hU 1
  exact (hG.mul (hT.sub (hhy.div hh hne))).add (hJ.div hh hne)

theorem height_energy_quotient_pos (E h : ℝ) (hE : 0 < E) (hh : h ≠ 0) :
    0 < E / h ^ 2 :=
  div_pos hE (sq_pos_of_ne_zero hh)

end SmoothLocal.Geometry

end

end OAI

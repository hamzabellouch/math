import OAI.Geometry.SurfaceImmersion.Geometry.CubicTaylorRemainder
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicCalculus
import OAI.Geometry.SurfaceImmersion.Geometry.ParameterIntegralDerivatives

namespace OAI

/-! Cubic Taylor remainders retain all weighted spatial derivative bounds
under integration in the variation parameter. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.ParameterTaylor
open SmoothPeriodicCalculus SmoothParameterIntegral WeightedEstimates

variable {A E : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def parameterJet : ℕ → (A × ℝ → E) → A × ℝ → E
  | 0, F => F
  | j + 1, F => angleDerivative (parameterJet j F)

lemma parameterJet_smooth {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (j : ℕ) :
    ContDiff ℝ ∞ (parameterJet j F) := by
  induction j with
  | zero => exact hF
  | succ j ih => exact contDiff_angleDerivative ih

lemma parameterJet_apply {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (j : ℕ) (p : A) (t : ℝ) :
    parameterJet j F (p, t) = iteratedDeriv j (fun r => F (p, r)) t := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    change angleDerivative (parameterJet j F) (p, t) = _
    rw [← (angle_hasDerivAt (parameterJet_smooth hF j) p t).deriv]
    have he : (fun r => parameterJet j F (p, r)) = iteratedDeriv j (fun r => F (p, r)) := funext ih
    rw [he, ← iteratedDeriv_succ]

def cubicRemainder (F : A × ℝ → E) (p : A) : E :=
  F (p, 1) - F (p, 0) - parameterJet 1 F (p, 0) - (1 / 2 : ℝ) • parameterJet 2 F (p, 0)

lemma cubicRemainder_smooth {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (cubicRemainder F) :=
  (((hF.comp (contDiff_id.prodMk contDiff_const)).sub
    (hF.comp (contDiff_id.prodMk contDiff_const))).sub
    ((parameterJet_smooth hF 1).comp (contDiff_id.prodMk contDiff_const))).sub
    (((parameterJet_smooth hF 2).comp (contDiff_id.prodMk contDiff_const)).const_smul (1 / 2 : ℝ))

variable [CompleteSpace E]

lemma cubicRemainder_eq_integral {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (p : A) :
    cubicRemainder F p = ∫ t in (0 : ℝ)..1, ((1 - t) ^ 2 / 2) • parameterJet 3 F (p, t) := by
  have hslice : ContDiff ℝ ∞ (fun t => F (p, t)) := hF.comp (contDiff_const.prodMk contDiff_id)
  simp only [cubicRemainder, parameterJet_apply hF, iteratedDeriv_one]
  exact cubicTaylor_remainder hslice

variable [FiniteDimensional ℝ A]

/-- A uniform weighted estimate for the third variation gives the same
weighted estimate for the actual nonlinear Taylor remainder. -/
theorem weighted_cubicRemainder {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F)
    {U : Set A} (hU : IsOpen U) {s M : ℝ} (hs : 0 < s) (hM : 0 ≤ M) (m : ℕ)
    (hb : ∀ j ≤ m, ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      s ^ j * ‖partialIterated j (parameterJet 3 F) (p, t)‖ ≤ M) :
    WeightedBound U s m (M / 2) (cubicRemainder F) := by
  let R : A × ℝ → E := fun z => ((1 - z.2) ^ 2 / 2) • parameterJet 3 F z
  have hJ := parameterJet_smooth hF 3
  have hR : ContDiff ℝ ∞ R :=
    (((contDiff_const.sub contDiff_snd).pow 2).div_const 2).smul hJ
  have hi := weighted_parameter_integral (C := M / 2) hR hU hs m 0 1
  have hbound : WeightedBound U s m ((M / 2) * |1 - 0|) (fun p => ∫ t in (0 : ℝ)..1, R (p, t)) := by
    apply hi
    intro j hj p hp t ht
    have htp : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hpart : partialIterated j R (p, t) =
        ((1 - t) ^ 2 / 2) • partialIterated j (parameterJet 3 F) (p, t) := by
      change iteratedFDeriv ℝ j (fun q => ((1 - t) ^ 2 / 2) • parameterJet 3 F (q, t)) p = _
      exact iteratedFDeriv_const_smul_apply'
        (((hJ.comp (contDiff_id.prodMk contDiff_const)).of_le
          (by simp : (j : ℕ∞ω) ≤ ∞)).contDiffAt)
    rw [hpart, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 - t) ^ 2 / 2)]
    have hw : (1 - t) ^ 2 / 2 ≤ (1 / 2 : ℝ) := by nlinarith [htp.1, htp.2]
    calc
      _ = ((1 - t) ^ 2 / 2) * (s ^ j * ‖partialIterated j (parameterJet 3 F) (p, t)‖) := by ring
      _ ≤ ((1 - t) ^ 2 / 2) * M := mul_le_mul_of_nonneg_left (hb j hj p hp t htp) (by positivity)
      _ ≤ (1 / 2 : ℝ) * M := mul_le_mul_of_nonneg_right hw hM
      _ = M / 2 := by ring
  have he : (fun p => ∫ t in (0 : ℝ)..1, R (p, t)) = cubicRemainder F := by
    funext p
    exact (cubicRemainder_eq_integral hF p).symm
  simpa only [he, sub_zero, abs_one, mul_one] using hbound

end ClosedSurfaceR4.ParameterTaylor

end

end OAI

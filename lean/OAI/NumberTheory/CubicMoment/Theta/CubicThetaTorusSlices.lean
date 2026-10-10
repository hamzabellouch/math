import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTorusModes
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Fourier coefficients of L2 cusp slices. The finite Bessel bounds and
Parseval identity justify the square-summable family of radial L2 modes. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CubicFirstMoment

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Countable Eisenstein := cubicThetaFourierIndex.injective.countable

abbrev CubicThetaCuspSlices := Lp CubicThetaTorusL2 2 (volume : Measure ℝ)

def cubicThetaTorusCoefficientMap (h : Eisenstein) : CubicThetaTorusL2 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : Fin 2 → ℤ => ℂ) 2 (cubicThetaFourierIndex h)).comp
    UnitAddTorus.mFourierBasis.repr.toLinearIsometry.toContinuousLinearMap

lemma cubicThetaTorusCoefficientMap_apply (h : Eisenstein) (F : CubicThetaTorusL2) :
    cubicThetaTorusCoefficientMap h F=cubicThetaTorusCoefficient F h :=
  UnitAddTorus.mFourierBasis_repr F _

def cubicThetaSliceCoefficient (h : Eisenstein) : CubicThetaCuspSlices →L[ℂ] CubicThetaRadialL2 :=
  (cubicThetaTorusCoefficientMap h).compLpL 2 volume

lemma cubicThetaSliceCoefficient_coe (h : Eisenstein) (F : CubicThetaCuspSlices) :
    cubicThetaSliceCoefficient h F =ᵐ[volume] (fun t => cubicThetaTorusCoefficient (F t) h) := by
  simpa only [cubicThetaSliceCoefficient,cubicThetaTorusCoefficientMap_apply] using
    (cubicThetaTorusCoefficientMap h).coeFn_compLpL F

lemma cubicThetaSliceCoefficient_integrable (F : CubicThetaCuspSlices) (h : Eisenstein) :
    Integrable (fun t => ‖cubicThetaTorusCoefficient (F t) h‖^2) := by
  have hm := (cubicThetaTorusCoefficientMap h).comp_memLp F
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  simpa only [Function.comp_apply,cubicThetaTorusCoefficientMap_apply] using hi

lemma cubicThetaSliceCoefficient_norm_sq (F : CubicThetaCuspSlices) (h : Eisenstein) :
    ‖cubicThetaSliceCoefficient h F‖^2=
      ∫ t : ℝ, ‖cubicThetaTorusCoefficient (F t) h‖^2 := by
  rw [cubicTheta_l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [cubicThetaSliceCoefficient_coe h F] with t ht
  rw [ht]

lemma cubicThetaTorus_finite_bessel (F : CubicThetaTorusL2) (s : Finset Eisenstein) :
    (∑ h ∈ s, ‖cubicThetaTorusCoefficient F h‖^2) ≤ ‖F‖^2 := by
  rw [← cubicThetaTorus_parseval F]
  exact (cubicThetaTorus_coefficients_summable F).sum_le_tsum s (fun _ _ => sq_nonneg _)

lemma cubicThetaSlices_finite_bessel (F : CubicThetaCuspSlices) (s : Finset Eisenstein) :
    (∑ h ∈ s, ‖cubicThetaSliceCoefficient h F‖^2) ≤ ‖F‖^2 := by
  simp_rw [cubicThetaSliceCoefficient_norm_sq]
  rw [← integral_finsetSum s (fun h _ => cubicThetaSliceCoefficient_integrable F h),cubicTheta_l2_norm_sq]
  apply integral_mono
    (integrable_finsetSum s (fun h _ => cubicThetaSliceCoefficient_integrable F h))
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp F).aestronglyMeasurable).mp (Lp.memLp F))
  intro t
  exact cubicThetaTorus_finite_bessel (F t) s

lemma cubicThetaSlices_coefficients_summable (F : CubicThetaCuspSlices) :
    Summable (fun h : Eisenstein => ‖cubicThetaSliceCoefficient h F‖^2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (cubicThetaSlices_finite_bessel F)

theorem cubicThetaSlices_parseval (F : CubicThetaCuspSlices) :
    (∑' h : Eisenstein, ‖cubicThetaSliceCoefficient h F‖^2)=‖F‖^2 := by
  have hs : Summable (fun h : Eisenstein => ∫ t : ℝ,
      ‖‖cubicThetaTorusCoefficient (F t) h‖^2‖) := by
    have he : (fun h : Eisenstein => ∫ t : ℝ, ‖‖cubicThetaTorusCoefficient (F t) h‖^2‖)=
        (fun h => ‖cubicThetaSliceCoefficient h F‖^2) := by
      funext h
      rw [cubicThetaSliceCoefficient_norm_sq]
      apply integral_congr_ae
      filter_upwards with t
      exact Real.norm_of_nonneg (sq_nonneg _)
    rw [he]
    exact cubicThetaSlices_coefficients_summable F
  calc
    _ = ∑' h : Eisenstein, ∫ t : ℝ, ‖cubicThetaTorusCoefficient (F t) h‖^2 := by
      simp_rw [cubicThetaSliceCoefficient_norm_sq]
    _ = ∫ t : ℝ, ∑' h : Eisenstein, ‖cubicThetaTorusCoefficient (F t) h‖^2 :=
      integral_tsum_of_summable_integral_norm (cubicThetaSliceCoefficient_integrable F) hs
    _ = ∫ t : ℝ, ‖F t‖^2 := by simp_rw [cubicThetaTorus_parseval]
    _ = _ := (cubicTheta_l2_norm_sq F).symm

end CubicFirstMoment

end

end OAI

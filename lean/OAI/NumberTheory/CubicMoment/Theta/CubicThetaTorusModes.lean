import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierMode
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergyNorm
import Mathlib.Analysis.Fourier.AddCircleMulti

namespace OAI

/-! The actual trace frequencies are the full Fourier basis of the
three-Eisenstein period cell. This fixes the lattice index and Parseval
normalization for the cusp Hilbert space. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CubicFirstMoment

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def cubicThetaFourierIndex : Eisenstein ≃ (Fin 2 → ℤ) :=
  (dualIntegerEquiv.trans coordinatesEquiv.toEquiv).symm

def cubicThetaPeriodCell (x : Fin 2 → ℝ) : ℂ := 3*eisensteinRealCoords x

lemma cubicTheta_trace_period_cell (h : Eisenstein) (x : Fin 2 → ℝ) :
    tracePair (cubicThetaPeriodCell x) (cubicThetaRowFrequency h)=
      ∑ i, x i*(cubicThetaFourierIndex h i:ℝ) := by
  have he : dualRealCoords (fun i => (cubicThetaFourierIndex h i:ℝ))=(h:ℂ)/traceLambda := by
    rw [dualRealCoords_integer]
    congr 1
    exact congrArg (fun h : Eisenstein => (h:ℂ)) (cubicThetaFourierIndex.symm_apply_apply h)
  rw [← dualRealCoords_trace,he]
  unfold tracePair cubicThetaPeriodCell cubicThetaRowFrequency
  congr 2
  field_simp

lemma cubicTheta_torus_fourier_real (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    UnitAddTorus.mFourier n (fun i => (x i:UnitAddCircle))=
      (Real.fourierChar (∑ i, x i*(n i:ℝ)):ℂ) := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Fin.prod_univ_two,
    fourier_coe_apply,Fin.sum_univ_two,Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def cubicThetaTorusFourier (h : Eisenstein) : C(UnitAddTorus (Fin 2),ℂ) :=
  UnitAddTorus.mFourier (cubicThetaFourierIndex h)

lemma cubicThetaTorusFourier_actual (h : Eisenstein) (x : Fin 2 → ℝ) :
    cubicThetaTorusFourier h (fun i => (x i:UnitAddCircle))=
      (Real.fourierChar (tracePair (cubicThetaPeriodCell x) (cubicThetaRowFrequency h)):ℂ) := by
  rw [cubicTheta_trace_period_cell]
  exact cubicTheta_torus_fourier_real _ _

abbrev CubicThetaTorusL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

def cubicThetaTorusCoefficient (F : CubicThetaTorusL2) (h : Eisenstein) : ℂ :=
  UnitAddTorus.mFourierCoeff F (cubicThetaFourierIndex h)

theorem cubicThetaTorus_parseval (F : CubicThetaTorusL2) :
    (∑' h : Eisenstein, ‖cubicThetaTorusCoefficient F h‖^2)=‖F‖^2 := by
  calc
    _ = ∑' n : Fin 2 → ℤ, ‖UnitAddTorus.mFourierCoeff F n‖^2 :=
      cubicThetaFourierIndex.tsum_eq _
    _ = ∫ t, ‖F t‖^2 := (UnitAddTorus.hasSum_sq_mFourierCoeff F).tsum_eq
    _ = _ := (cubicTheta_l2_norm_sq_measure F).symm

theorem cubicThetaTorus_coefficients_summable (F : CubicThetaTorusL2) :
    Summable (fun h : Eisenstein => ‖cubicThetaTorusCoefficient F h‖^2) :=
  cubicThetaFourierIndex.summable_iff.mpr (UnitAddTorus.hasSum_sq_mFourierCoeff F).summable

end CubicFirstMoment

end

end OAI

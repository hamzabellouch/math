import Mathlib
import OAI.Analysis.Conductivity.Variational.CrossingEstimates
import OAI.Analysis.Conductivity.Variational.ScaledSmoothSeries

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma crossingResidualFirst_smooth (L : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingResidualFirst L) :=
  (smooth_deriv_infty (smooth_deriv_infty (crossingFirst_smooth L))).sub
    (contDiff_const.mul (crossingFirst_smooth L))
lemma crossingResidualSecond_smooth (L : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (crossingResidualSecond L) :=
  (smooth_deriv_infty (smooth_deriv_infty (crossingSecond_smooth L))).sub (crossingSecond_smooth L)

lemma crossingResidualFirst_zero_right {L z : ℝ} (hL : 0 < L) (hz : 3*L/4 < z) :
    crossingResidualFirst L z = 0 := by
  have hu : 1 < 4*z/L-2 := by
    have : 3 < 4*z/L := (lt_div_iff₀ hL).mpr (by linarith)
    linarith
  rw [crossingResidualFirst_formula,crossingOff_second]
  simp only [deriv_crossingOff,(smoothTransition_flat_right hu).1,(smoothTransition_flat_right hu).2]
  ring
lemma crossingResidualSecond_zero_left {L z : ℝ} (hL : 0 < L) (hz : z < -3*L/4) :
    crossingResidualSecond L z = 0 := by
  have hu : 4*z/L+3 < 0 := by
    have : 4*z/L < -3 := (div_lt_iff₀ hL).mpr (by linarith)
    linarith
  rw [crossingResidualSecond_formula,crossingOn_second]
  simp only [deriv_crossingOn,(smoothTransition_flat_left hu).1,(smoothTransition_flat_left hu).2]
  ring

lemma crossingResidualFirst_compact {L : ℝ} (hL : 0 < L) : HasCompactSupport (crossingResidualFirst L) := by
  apply HasCompactSupport.intro (K := Icc (L/2) (3*L/4)) isCompact_Icc
  intro z hz
  simp only [mem_Icc,not_and_or,not_le] at hz
  exact hz.elim (crossingResidualFirst_zero hL) (crossingResidualFirst_zero_right hL)
lemma crossingResidualSecond_compact {L : ℝ} (hL : 0 < L) : HasCompactSupport (crossingResidualSecond L) := by
  apply HasCompactSupport.intro (K := Icc (-3*L/4) (-L/2)) isCompact_Icc
  intro z hz
  simp only [mem_Icc,not_and_or,not_le] at hz
  exact hz.elim (crossingResidualSecond_zero_left hL) (crossingResidualSecond_zero hL)

def cascadeBaseStream (L K : ℝ) (a : Fin 3) (x : Coord3) : ℝ :=
  deriv (cascadeProfile L K) (x 0)*sin (x a)

def cascadeCrossStream (L K : ℝ) (a b : Fin 3) (x : Coord3) : ℝ :=
  connectorProfile K (K+2)*exp (-3*L)*
    (crossingResidualFirst L (x 0-(K+2+L))/4*sin (4*x b)*sin (x a) -
      crossingResidualSecond L (x 0-(K+2+L))/2*cos (x a)*sin (x a)*sin (2*x b))

lemma cascadeBaseStream_bounded {L K : ℝ} (hL : 0 < L) (a : Fin 3) :
    BoundedSmooth (cascadeBaseStream L K a) := by
  let P : Fin 3 → Coord3 →L[ℝ] ℝ := fun i => ContinuousLinearMap.proj i
  exact ((BoundedSmooth.of_compact (smooth_deriv_infty (cascadeProfile_smooth L K))
    (cascadeProfile_compact hL).deriv).comp_linear (P 0)).mul
    (sin_boundedSmooth.comp_linear (P a))

lemma cascadeCrossStream_bounded {L K : ℝ} (hL : 0 < L) (a b : Fin 3) :
    BoundedSmooth (cascadeCrossStream L K a b) := by
  let P : Fin 3 → Coord3 →L[ℝ] ℝ := fun i => ContinuousLinearMap.proj i
  have hf := (((BoundedSmooth.of_compact (crossingResidualFirst_smooth L)
    (crossingResidualFirst_compact hL)).translate (K+2+L)).comp_linear (P 0)).smul (1/4)
  have hg := (((BoundedSmooth.of_compact (crossingResidualSecond_smooth L)
    (crossingResidualSecond_compact hL)).translate (K+2+L)).comp_linear (P 0)).smul (1/2)
  have hs₁ := sin_boundedSmooth.comp_linear (4 • P b)
  have hs₂ := sin_boundedSmooth.comp_linear (2 • P b)
  have hsa := sin_boundedSmooth.comp_linear (P a)
  have hca := cos_boundedSmooth.comp_linear (P a)
  convert (((hf.mul hs₁).mul hsa).sub (((hg.mul hca).mul hsa).mul hs₂)).smul
    (connectorProfile K (K+2)*exp (-3*L)) using 1
  funext x
  simp only [cascadeCrossStream,Function.comp_def,smul_apply,P,
    ContinuousLinearMap.proj_apply]
  ring_nf

end ScalarConductivity

end

end OAI

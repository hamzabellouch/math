import Mathlib
import OAI.Analysis.Conductivity.Geometry.BoxIteration
import OAI.Analysis.Conductivity.Geometry.TorusFaceIntegration
import OAI.Analysis.Conductivity.Fourier.AngularIntegratedTrace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma sourceExtendedBox_compact (l r : ℝ) : IsCompact (sourceExtendedBox l r) := isCompact_Icc

theorem sourceExtended_integral_bound {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x))≤
      100*(∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y) := by
  rw [sourceExtended_integral i j hl hr,←integral_const_mul]
  apply setIntegral_mono_on
  · exact (hg.comp (sourceCollarPiece_contDiff i j).continuous).continuousOn.integrableOn_compact isCompact_Icc
  · have hc : Continuous (fun x : Fin 3 → ℝ => abs ((sourceCollarDerivative i j x).det)) := by
      simp_rw [sourceCollarDerivative_det]
      unfold sourceCollarRadius squareFace
      fun_prop
    exact (continuous_const.mul (hc.mul (hg.comp (sourceCollarPiece_contDiff i j).continuous))).continuousOn.integrableOn_compact isCompact_Icc
  · exact measurableSet_Icc
  · intro x hx
    have hh := sourceExtended_jacobian_lower i j hl hr hx
    change g (sourceCollarPiece i j x)≤100*(abs ((sourceCollarDerivative i j x).det)*g (sourceCollarPiece i j x))
    nlinarith [mul_nonneg (hn (sourceCollarPiece i j x)) (show 0≤abs ((sourceCollarDerivative i j x).det)-1/100 by linarith)]

lemma continuous_collarFace_integral {g : (Fin 3 → ℝ) → ℝ} (hg : Continuous g) (i j : Fin 4) :
    Continuous (fun t : ℝ => ∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b])) := by
  apply continuous_parametric_unitInterval (f:=fun t a => ∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b]))
  apply continuous_parametric_unitInterval (f:=fun p : ℝ×ℝ => fun b => g (sourceCollarPiece i j ![p.1,p.2,b]))
  exact hg.comp ((sourceCollarPiece_contDiff i j).continuous.comp (by fun_prop))

theorem sourceAngular_volume_bound {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) {l r : ℝ}
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    (∫ t in l..r,∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x))≤
      (100*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi)))*
        ∑ i : Fin 4,∑ j : Fin 4,∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y := by
  let c : ℝ := ((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi))
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hc : 0≤c := by dsimp [c]; positivity
  have hcont : Continuous (fun t : ℝ => ∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x)) := by
    have hcs : Continuous (fun p : ℝ×UnitAddTorus (Fin 2) => sourceAngularCollar p.1 p.2) := by
      simpa only [zero_add] using continuous_sourceAngular 0
    have hh := continuous_parametric_integral_of_continuous (μ:=volume)
      (f:=fun t (x : UnitAddTorus (Fin 2)) => g (sourceAngularCollar t x))
      (hg.comp hcs) (s:=univ) isCompact_univ
    simpa using hh
  have hsum : Continuous (fun t : ℝ => ∑ i : Fin 4,∑ j : Fin 4,
      ∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b])) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => continuous_collarFace_integral hg i j))
  calc
    _≤∫ t in l..r,c*(∑ i : Fin 4,∑ j : Fin 4,
        ∫ a in (-1:ℝ)..1,∫ b in (-1:ℝ)..1,g (sourceCollarPiece i j ![t,a,b])) :=
      intervalIntegral.integral_mono_on hlr (hcont.intervalIntegrable l r)
        ((continuous_const.mul hsum).intervalIntegrable l r) (fun t _ => integral_sourceAngular_le hg hn t)
    _=c*(∑ i : Fin 4,∑ j : Fin 4,∫ x in sourceExtendedBox l r,g (sourceCollarPiece i j x)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_finsetSum (fun i _ =>
        (continuous_finsetSum _ (fun j _ => continuous_collarFace_integral hg i j)).intervalIntegrable l r)]
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finsetSum (fun j _ => (continuous_collarFace_integral hg i j).intervalIntegrable l r)]
      apply Finset.sum_congr rfl
      intro j _
      exact (integral_sourceExtendedBox (hg.comp (sourceCollarPiece_contDiff i j).continuous) hlr).symm
    _≤c*(∑ i : Fin 4,∑ j : Fin 4,100*(∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact sourceExtended_integral_bound hg hn i j hl hr
    _=_ := by simp_rw [←Finset.mul_sum]; dsimp [c]; ring

end ScalarConductivity

end

end OAI

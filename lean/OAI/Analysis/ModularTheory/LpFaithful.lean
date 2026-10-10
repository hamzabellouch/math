import OAI.Analysis.ModularTheory.LpRepresentation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! Faithfulness of the concrete modular representation for Lebesgue measure.
The fixed interval [0,1] gives an isometric copy of the original Hilbert space
and detects every constant operator before gauge conjugation. -/

noncomputable section
open MeasureTheory Set

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def lpIntervalVector (x : H) : Lp H 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) (by simp) x

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma lpIntervalVector_norm (x : H) : ‖lpIntervalVector x‖ = ‖x‖ := by
  rw [lpIntervalVector, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [Measure.real]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma lpIntervalVector_sub (x y : H) :
    lpIntervalVector x - lpIntervalVector y = lpIntervalVector (x - y) :=
  indicatorConstLp_sub

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma lpIntervalVector_injective : Function.Injective (lpIntervalVector (H := H)) := by
  intro x y h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← lpIntervalVector_norm, ← lpIntervalVector_sub, h, sub_self, norm_zero]

lemma pointwiseLpRepresentation_interval (T : H →L[ℂ] H) (x : H) :
    pointwiseLpRepresentation (volume : Measure ℝ) T (lpIntervalVector x) =
      lpIntervalVector (T x) := by
  apply Lp.ext
  filter_upwards [T.coeFn_compLpL (p := 2) (μ := (volume : Measure ℝ)) (lpIntervalVector x),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc (a := (0 : ℝ)) (b := 1))
      (hμs := by simp) (c := x),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc (a := (0 : ℝ)) (b := 1))
      (hμs := by simp) (c := T x)] with t hT hx hTx
  change (T.compLpL 2 volume (lpIntervalVector x)) t = (lpIntervalVector (T x)) t
  change lpIntervalVector x t = (Ioc 0 1).indicator (fun _ => x) t at hx
  change lpIntervalVector (T x) t = (Ioc 0 1).indicator (fun _ => T x) t at hTx
  rw [hT, hx, hTx]
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht, map_zero]

theorem pointwiseLpRepresentation_injective :
    Function.Injective (pointwiseLpRepresentation (H := H) (volume : Measure ℝ)) := by
  intro T R hTR
  apply ContinuousLinearMap.ext
  intro x
  apply lpIntervalVector_injective
  rw [← pointwiseLpRepresentation_interval, ← pointwiseLpRepresentation_interval, hTR]

theorem modularLpRepresentation_injective (D : BoundedRecovery.RealSpectralCalculus H) :
    Function.Injective (modularLpRepresentation (volume : Measure ℝ) D) := by
  intro T R hTR
  apply pointwiseLpRepresentation_injective
  apply (D.lpGaugeEquiv volume (-1)).conjStarAlgEquiv.injective
  exact hTR

end WeakPureInfiniteness

end

end OAI

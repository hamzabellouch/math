import OAI.Analysis.KadisonKastler.ScalarPullbackWeakGraph
import OAI.Analysis.KadisonKastler.ScalarShiftCesaro

namespace OAI

/-! # The invariant scalar limit of shift averages

One common ultrafilter yields a contractive linear limit of the Cesaro
operators. The telescoping estimate and weak closure of the nonsingular
pullback graph force every value of the limit to be shift invariant.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  (S : X → X) (hS : Measure.QuasiMeasurePreserving S μ μ)

theorem scalarShiftCesaro_difference_tendsto_zero (f : ScalarLInfinity μ) :
    Tendsto (fun n => scalarInfinityPullback S hS (scalarShiftCesaro S hS n f) -
      scalarShiftCesaro S hS n f) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hrate : Tendsto (fun n : ℕ => 2 * ((n + 1 : ℕ) : ℝ)⁻¹ * ‖f‖) atTop (𝓝 0) := by
    simpa only [one_div, Nat.cast_add, Nat.cast_one, mul_zero, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2).mul_const ‖f‖
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => scalarShiftCesaro_difference_norm_le S hS n f)
    hrate

theorem scalarShiftCesaro_weak_limit_fixed
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (f b : ScalarLInfinity μ)
    (hb : ∀ y, Tendsto (fun n => inner ℂ y (scalarInfinityToL2 (scalarShiftCesaro S hS n f)))
      (ω : Filter ℕ) (𝓝 (inner ℂ y (scalarInfinityToL2 b)))) :
    scalarInfinityPullback S hS b = b := by
  have hd := (scalarInfinityToL2L (μ := μ)).continuous.tendsto 0 |>.comp
    ((scalarShiftCesaro_difference_tendsto_zero S hS f).mono_left hω)
  have hd' : Tendsto (fun n => scalarInfinityToL2
      (scalarInfinityPullback S hS (scalarShiftCesaro S hS n f)) -
        scalarInfinityToL2 (scalarShiftCesaro S hS n f)) (ω : Filter ℕ) (𝓝 0) := by
    simpa only [Function.comp_def, map_sub, map_zero, scalarInfinityToL2L_apply] using hd
  have hg (y : Lp ℂ 2 μ) : Tendsto (fun n => inner ℂ y (scalarInfinityToL2
      (scalarInfinityPullback S hS (scalarShiftCesaro S hS n f)))) (ω : Filter ℕ)
      (𝓝 (inner ℂ y (scalarInfinityToL2 b))) := by
    have hc : Continuous (fun z : Lp ℂ 2 μ => inner ℂ y z) :=
      continuous_const.inner continuous_id
    have hh := (hc.tendsto (0 : Lp ℂ 2 μ)).comp hd'
    have hh' := hh.add (hb y)
    simpa only [Function.comp_def, inner_zero_right, zero_add, inner_sub_right, sub_add_cancel] using hh'
  exact scalarInfinityPullback_of_weak_limits S hS
    (fun n => scalarShiftCesaro S hS n f)
    (fun n => scalarInfinityPullback S hS (scalarShiftCesaro S hS n f)) b b
    (fun _ => rfl) hb hg

theorem exists_scalar_shift_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E →L[ℂ] ScalarLInfinity μ) (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) :
    ∃ B : E →L[ℂ] ScalarLInfinity μ, (∀ x, ‖B x‖ ≤ ‖x‖) ∧
      (∀ x, scalarInfinityPullback S hS (B x) = B x) ∧
      ∀ x y, Tendsto (fun n => inner ℂ y (scalarInfinityToL2 (scalarShiftCesaro S hS n (J x))))
        (Ultrafilter.of (atTop : Filter ℕ) : Filter ℕ)
        (𝓝 (inner ℂ y (scalarInfinityToL2 (B x)))) := by
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨B, hB, ht⟩ := exists_scalar_linear_weak_ultralimit ω
    (fun n => (scalarShiftCesaro S hS n).comp J)
    (fun n x => (scalarShiftCesaro_norm_le S hS n (J x)).trans (hJ x))
  refine ⟨B, hB, ?_, ht⟩
  intro x
  exact scalarShiftCesaro_weak_limit_fixed S hS ω (Ultrafilter.of_le atTop) (J x) (B x) (ht x)

end

end KadisonKastler

end OAI

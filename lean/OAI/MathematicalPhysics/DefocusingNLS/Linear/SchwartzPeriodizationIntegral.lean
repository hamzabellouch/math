import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPeriodizationFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-! # Integration of the genuine lattice periodization

The fundamental-cell integral of a periodized Schwartz function, twisted by
a periodic unit-modulus character, is its whole-space integral.
-/

open Set MeasureTheory TopologicalSpace
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

instance frequencyLattice_vaddInvariant_volume :
    VAddInvariantMeasure frequencyLattice E (volume : Measure E) where
  measure_preimage_vadd n s _ := by
    change volume ((fun x : E => (n : E) + x) ⁻¹' s) = volume s
    exact measure_preimage_add volume (n : E) s

noncomputable def frequencyCell : Set E :=
  ZSpan.fundamentalDomain (EuclideanSpace.basisFun (Fin 12) ℝ).toBasis

theorem frequencyCell_isAddFundamentalDomain :
    IsAddFundamentalDomain frequencyLattice frequencyCell (volume : Measure E) := by
  exact ZSpan.isAddFundamentalDomain (EuclideanSpace.basisFun (Fin 12) ℝ).toBasis volume

theorem frequencyCell_isBounded : Bornology.IsBounded frequencyCell :=
  ZSpan.fundamentalDomain_isBounded _

theorem frequencyCell_measurableSet : MeasurableSet frequencyCell :=
  ZSpan.fundamentalDomain_measurableSet _

theorem frequencyCell_volume_lt_top : volume frequencyCell < ⊤ :=
  (measure_mono subset_closure).trans_lt frequencyCell_isBounded.isCompact_closure.measure_lt_top

theorem schwartzPeriodization_twisted_integral (K : 𝓢(E, ℂ)) (e : C(E, ℂ))
    (he : ∀ x, ‖e x‖ = 1)
    (hperiod : ∀ (x : E) (n : frequencyLattice), e (x + n) = e x) :
    (∫ x in frequencyCell, e x * schwartzPeriodization K x) = ∫ x, e x * K x := by
  let S : Compacts E := ⟨closure frequencyCell, frequencyCell_isBounded.isCompact_closure⟩
  have hI (n : frequencyLattice) :
      IntegrableOn (fun x : E => e x * K (x + n)) frequencyCell := by
    have hc : Continuous (fun x : E => e x * K (x + n)) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact S.isCompact).mono_set subset_closure
  have hnorm (n : frequencyLattice) (x : E) : ‖e x * K (x + n)‖ = ‖K (x + n)‖ := by
    rw [norm_mul, he, one_mul]
  have hsum : Summable (fun n : frequencyLattice =>
      ∫ x in frequencyCell, ‖e x * K (x + n)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
      ((summable_schwartzLatticeTranslate_restrict K S).mul_right (volume.real frequencyCell))
    intro n
    rw [← Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    apply norm_setIntegral_le_of_norm_le_const frequencyCell_volume_lt_top
    intro x hx
    rw [norm_norm, hnorm]
    exact ((schwartzLatticeTranslate K n).restrict S).norm_coe_le_norm ⟨x, subset_closure hx⟩
  have hwhole : Integrable (fun x : E => e x * K x) := by
    apply K.integrable.bdd_mul e.continuous.aestronglyMeasurable
    filter_upwards [] with x
    exact (he x).le
  calc
    _ = ∫ x in frequencyCell, ∑' n : frequencyLattice, e x * K (x + n) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [schwartzPeriodization_apply, tsum_mul_left]
    _ = ∑' n : frequencyLattice, ∫ x in frequencyCell, e x * K (x + n) :=
      (integral_tsum_of_summable_integral_norm hI hsum).symm
    _ = ∑' n : frequencyLattice, ∫ x in frequencyCell, e ((n : E) + x) * K ((n : E) + x) := by
      apply tsum_congr
      intro n
      apply integral_congr_ae
      filter_upwards [] with x
      rw [add_comm (n : E) x, hperiod]
    _ = _ := (frequencyCell_isAddFundamentalDomain.integral_eq_tsum'' _ hwhole).symm

theorem schwartzPeriodization_integral (K : 𝓢(E, ℂ)) :
    (∫ x in frequencyCell, schwartzPeriodization K x) = ∫ x, K x := by
  simpa using schwartzPeriodization_twisted_integral K (1 : C(E, ℂ)) (by simp) (by simp)

end DefocusingNLS

end OAI

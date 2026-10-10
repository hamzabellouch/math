import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPeriodizationIntegral

namespace OAI

/-! # Integrating periodization against a bounded periodic function -/

open Set MeasureTheory TopologicalSpace
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem schwartzPeriodization_weighted_integral (K : 𝓢(E, ℂ)) (e : C(E, ℂ))
    (C : ℝ) (hC : 0 ≤ C) (he : ∀ x, ‖e x‖ ≤ C)
    (hperiod : ∀ (x : E) (n : frequencyLattice), e (x + n) = e x) :
    (∫ x in frequencyCell, e x * schwartzPeriodization K x) = ∫ x, e x * K x := by
  let S : Compacts E := ⟨closure frequencyCell, frequencyCell_isBounded.isCompact_closure⟩
  have hI (n : frequencyLattice) :
      IntegrableOn (fun x : E => e x * K (x + n)) frequencyCell := by
    have hc : Continuous (fun x : E => e x * K (x + n)) := by fun_prop
    exact (hc.continuousOn.integrableOn_compact S.isCompact).mono_set subset_closure
  have hsum : Summable (fun n : frequencyLattice =>
      ∫ x in frequencyCell, ‖e x * K (x + n)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
      (((summable_schwartzLatticeTranslate_restrict K S).mul_left C).mul_right
        (volume.real frequencyCell))
    intro n
    rw [← Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    apply norm_setIntegral_le_of_norm_le_const frequencyCell_volume_lt_top
    intro x hx
    rw [norm_norm, norm_mul]
    have hb := ((schwartzLatticeTranslate K n).restrict S).norm_coe_le_norm ⟨x, subset_closure hx⟩
    change ‖K (x + n)‖ ≤ ‖(schwartzLatticeTranslate K n).restrict S‖ at hb
    exact mul_le_mul (he x) hb (norm_nonneg _) hC
  have hwhole : Integrable (fun x : E => e x * K x) := by
    apply K.integrable.bdd_mul e.continuous.aestronglyMeasurable
    exact ae_of_all _ he
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

end DefocusingNLS

end OAI

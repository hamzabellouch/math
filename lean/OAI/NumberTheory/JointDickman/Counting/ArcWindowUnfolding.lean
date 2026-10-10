import OAI.NumberTheory.JointDickman.Counting.PeriodicWindowIntegral

namespace OAI

/-! # Exact unfolding of the clipped, closed major-arc windows -/

namespace JointDickman
open MeasureTheory Set

theorem closed_window_integral (L U : ℝ) (k : ℤ) (F : ℝ → ℂ) :
    (∫ x in {x : ℝ | x ∈ Ioc 0 1 ∧ L ≤ (k : ℝ)+x ∧ (k : ℝ)+x ≤ U}, F x) =
      ∫ x in Ioc (0 : ℝ) 1,
        if L < (k : ℝ)+x ∧ (k : ℝ)+x ≤ U then F x else 0 := by
  classical
  have hset : {x : ℝ | x ∈ Ioc 0 1 ∧ L ≤ (k : ℝ)+x ∧ (k : ℝ)+x ≤ U} =
      Ioc 0 1 ∩ Icc (L-k) (U-k) := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_Icc]
    constructor <;> rintro ⟨hx,hL,hU⟩ <;> exact ⟨hx,by linarith,by linarith⟩
  rw [hset]
  rw [setIntegral_congr_set
    (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl Ioc_ae_eq_Icc.symm)]
  rw [← setIntegral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [indicator_apply, mem_Ioc]
  congr 1
  apply propext
  constructor <;> rintro ⟨hL,hU⟩ <;> constructor <;> linarith

theorem periodic_closed_windows {F : ℝ → ℂ} (hF : Continuous F)
    (hp : Function.Periodic F 1) {L U : ℝ} (hLU : L ≤ U) :
    (∑' k : ℤ, ∫ x in
      {x : ℝ | x ∈ Ioc 0 1 ∧ L ≤ (k : ℝ)+x ∧ (k : ℝ)+x ≤ U}, F x) =
      ∫ x in L..U, F x := by
  simp_rw [closed_window_integral]
  exact (periodic_window_integral hF hp hLU).symm

end JointDickman

end OAI

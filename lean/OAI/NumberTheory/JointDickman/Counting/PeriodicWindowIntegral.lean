import OAI.NumberTheory.JointDickman.Counting.ArcCoefficientIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

/-! # Unfolding a compact window across the integer period -/

namespace JointDickman
open MeasureTheory Set

noncomputable def integerLatticeEquiv : ℤ ≃ AddSubgroup.zmultiples (1 : ℝ) :=
  Equiv.ofBijective (fun k => ⟨(k : ℝ),by
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨k,by simp⟩⟩) (by
      constructor
      · intro k l h
        have he := congrArg Subtype.val h
        change (k : ℝ) = (l : ℝ) at he
        exact_mod_cast he
      · intro x
        obtain ⟨k,hk⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
        refine ⟨k,Subtype.ext ?_⟩
        simpa only [zsmul_eq_mul,mul_one] using hk)

theorem integral_eq_integer_windows (f : ℝ → ℂ) (hf : Integrable f) :
    (∫ x : ℝ, f x) = ∑' k : ℤ, ∫ x in Ioc (0 : ℝ) 1, f (k+x) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0 : ℝ) < 1) 0).integral_eq_tsum'' f hf
  rw [← integerLatticeEquiv.tsum_eq] at h
  simp only [zero_add] at h
  refine h.trans ?_
  apply tsum_congr
  intro k
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  rfl

/-- A window crossing either endpoint of a period is recovered exactly by
its integer translates; no arc at zero is omitted or counted twice. -/
theorem periodic_window_integral {F : ℝ → ℂ} (hF : Continuous F)
    (hp : Function.Periodic F 1) {L U : ℝ} (hLU : L ≤ U) :
    (∫ x in L..U, F x) =
      ∑' k : ℤ, ∫ x in Ioc (0 : ℝ) 1,
        if L < (k : ℝ)+x ∧ (k : ℝ)+x ≤ U then F x else 0 := by
  classical
  have hi : Integrable ((Ioc L U).indicator F) :=
    ((hF.intervalIntegrable L U).1).integrable_indicator measurableSet_Ioc
  have h := integral_eq_integer_windows ((Ioc L U).indicator F) hi
  rw [integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le hLU] at h
  rw [h]
  apply tsum_congr
  intro k
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hk : F ((k : ℝ)+x) = F x := by
    have hh := hp.int_mul k x
    simpa only [mul_one,add_comm] using hh
  simp only [indicator_apply,mem_Ioc,hk]

end JointDickman

end OAI

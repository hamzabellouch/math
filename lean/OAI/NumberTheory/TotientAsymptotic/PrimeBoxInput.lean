import OAI.NumberTheory.TotientAsymptotic.MertensReciprocal
import OAI.NumberTheory.TotientAsymptotic.PrimeShiftWeight

namespace OAI

/-! Discharge of Ford's unit-box prime sum from the proved second Mertens theorem. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem fordUnitPrimeBoxInput : FordUnitPrimeBoxInput := by
  obtain ⟨D,hD,hbound⟩ := primeReciprocalLT_mertens
  refine ⟨D*(1+Real.exp 1)+2*Real.exp 1,by positivity,?_⟩
  intro m hm
  let a := Real.exp (Real.exp ((m : ℝ)-1))
  let b := Real.exp (Real.exp (m : ℝ))
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 2≤a := by
    have hh : Real.exp 1≤a := Real.exp_le_exp.mpr (Real.one_le_exp (by linarith))
    linarith [Real.exp_one_gt_d9]
  have hab : a≤b := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith))
  have hb : 2≤b := ha.trans hab
  have ha0 : 0<a := by linarith
  have hla : Real.log a=Real.exp ((m : ℝ)-1) := Real.log_exp _
  have hlb : Real.log b=Real.exp (m : ℝ) := Real.log_exp _
  have hlla : Real.log (Real.log a)=(m : ℝ)-1 := by rw [hla,Real.log_exp]
  have hllb : Real.log (Real.log b)=(m : ℝ) := by rw [hlb,Real.log_exp]
  have hmass : |primeReciprocalLT b-primeReciprocalLT a-1| ≤
      D/Real.log b+D/Real.log a := by
    calc
      _ = |(primeReciprocalLT b-Real.log (Real.log b)-Mertens.M)-
          (primeReciprocalLT a-Real.log (Real.log a)-Mertens.M)| := by
        rw [hlla,hllb]
        congr 1
        ring
      _ ≤ |primeReciprocalLT b-Real.log (Real.log b)-Mertens.M|+
          |primeReciprocalLT a-Real.log (Real.log a)-Mertens.M| := abs_sub _ _
      _ ≤ _ := add_le_add (hbound b hb) (hbound a ha)
  have he : |unitPrimeWeight m-(primeReciprocalLT b-primeReciprocalLT a)|≤2/a := by
    rw [← unitPrimeBox_reciprocal]
    exact shifted_reciprocal_error (unitPrimeBox m) ha
      (fun p hp => (Finset.mem_filter.mp hp).2.2.1)
  have hsmall : 2/a≤2/Real.log a := by
    apply div_le_div_of_nonneg_left (by norm_num) (Real.log_pos (by linarith))
    linarith [Real.log_le_sub_one_of_pos ha0]
  have htotal : |unitPrimeWeight m-1|≤D/Real.log b+(D+2)/Real.log a := by
    calc
      _ ≤ |unitPrimeWeight m-(primeReciprocalLT b-primeReciprocalLT a)|+
          |(primeReciprocalLT b-primeReciprocalLT a)-1| := abs_sub_le _ _ _
      _ ≤ 2/a+(D/Real.log b+D/Real.log a) := add_le_add he hmass
      _ ≤ 2/Real.log a+(D/Real.log b+D/Real.log a) := add_le_add hsmall le_rfl
      _ = _ := by ring
  have heq : D/Real.log b+(D+2)/Real.log a=
      (D*(1+Real.exp 1)+2*Real.exp 1)*Real.exp (-(m : ℝ)) := by
    rw [hla,hlb]
    simp only [div_eq_mul_inv,← Real.exp_neg]
    rw [show -((m : ℝ)-1)=1+ -(m : ℝ) by ring,Real.exp_add]
    ring
  exact heq ▸ htotal

end TotientAsymptotic

end

end OAI

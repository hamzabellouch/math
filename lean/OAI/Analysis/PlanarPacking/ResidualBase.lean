import OAI.Analysis.PlanarPacking.ExactJets
import OAI.Analysis.PlanarPacking.TableKBridge

namespace OAI

/-!
# Residuals of the cardinal interpolation equations

The finite coefficient families have small residuals in the exact interpolation equations.
-/

namespace SharpPlanar
open Numerical IntegerIntervals
noncomputable def tableResidual (a : Bool) : X :=
  if a then tableList true-S (tableList false)-g₂
  else tableList false-S (tableList true)-g₁
lemma tableResidual_apply (a : Bool) (n : Node) (d : Bool) :
    tableResidual a (n,d)=
      (if d then (tableD a n.val:ℝ) else (tableC a n.val:ℝ))-
      transformedJets (tableData (!a)) (n,d)+
      (if a=false ∧ n.val=1 ∧ d=true then 1 else 0) := by
  cases a
  · have h := transformedJets_fixed₂ (tableList true) (n,d)
    rw [← tableData_true] at h
    change tableList false (n,d)-S (tableList true) (n,d)-
      (transformedJets (fixed₂ 0) (n,d)-contactList (n,d))=_
    rw [tableList_apply,contactList_apply]
    simp only [Bool.not_false,true_and]
    rw [h]
    ring
  · have h := transformedJets_fixed₁ (tableList false) (n,d)
    rw [← tableData_false] at h
    change tableList true (n,d)-S (tableList false) (n,d)-
      transformedJets (fixed₁ 0) (n,d)=_
    rw [tableList_apply]
    simp only [Bool.not_true,Bool.true_eq_false,false_and,ite_false,add_zero]
    rw [h]
    ring
lemma tableResidual_value (a : Bool) (n : Node) :
    tableResidual a (n,false)=(tableC a n.val:ℝ)+tableMomentK (!a) n.val 0/(Q n.val) := by
  rw [tableResidual_apply]
  simp only [transformedJets,Bool.false_eq_true,ite_false,and_false,tableMomentK_eq,
    Nat.factorial_zero,Nat.cast_one,div_one,neg_div,sub_neg_eq_add,add_zero]
lemma tableResidual_deriv (a : Bool) (n : Node) :
    tableResidual a (n,true)=(tableD a n.val:ℝ)+
      (if a=false ∧ n.val=1 then 1 else 0)+
      (tableMomentK (!a) n.val 1-D n.val*tableMomentK (!a) n.val 0)/(Q n.val) := by
  rw [tableResidual_apply]
  simp only [transformedJets,ite_true,and_true,tableMomentK_eq,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one]
  ring
lemma RBox.abs_lt {a : RBox} {x : ℝ} {u v : ℤ} (hx : a.Contains x)
    (hv : 0<v) (hc : a.bound*v<precision*u) : |x|<(u:ℝ)/v := by
  have h1 := RBox.abs_bound hx
  have hv' : (0:ℝ)<v := by exact_mod_cast hv
  have h2 : (a.bound:ℝ)*v < (precision:ℝ)*u := by exact_mod_cast hc
  apply (mul_lt_mul_iff_right₀ precision_pos).mp
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hv').mpr
  exact (mul_le_mul_of_nonneg_right h1 hv'.le).trans_lt h2
end SharpPlanar

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.FiniteSchur
import Mathlib.Analysis.PSeries

namespace OAI

/-! Summable cubic separation of dyadic measure classes, with a finite
convolution bound uniform in the number and range of classes. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def measureClassKernel (k : ℤ) : ℝ := (((k.natAbs:ℝ)+1)^3)⁻¹

theorem measureClassKernel_nonneg (k : ℤ) : 0≤measureClassKernel k := by
  unfold measureClassKernel
  positivity

theorem measureClassKernel_neg (k : ℤ) : measureClassKernel (-k)=measureClassKernel k := by
  simp only [measureClassKernel,Int.natAbs_neg]

theorem measureClassKernel_summable : Summable measureClassKernel := by
  have h : Summable (fun n : ℕ => ((n:ℝ)^3)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  have hs : Summable (fun n : ℕ => (((n:ℝ)+1)^3)⁻¹) := by
    simpa only [Function.comp_def,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using h.comp_injective Nat.succ_injective
  apply Summable.of_nat_of_neg
  · simpa only [measureClassKernel,Int.natAbs_natCast] using hs
  · simpa only [measureClassKernel,Int.natAbs_neg,Int.natAbs_natCast] using hs

theorem measureClassKernel_shift_sum_le (S : Finset ℤ) (a : ℤ) :
    (∑ k∈S, measureClassKernel (k-a))≤∑' k, measureClassKernel k := by
  classical
  have he : (∑ k∈S.image (fun k => k-a), measureClassKernel k)=
      ∑ k∈S, measureClassKernel (k-a) :=
    Finset.sum_image (g:=fun k : ℤ => k-a) (fun i _ j _ hij => by
      change i-a=j-a at hij
      omega)
  rw [←he]
  exact measureClassKernel_summable.sum_le_tsum _ (fun k _ => measureClassKernel_nonneg k)

theorem measure_class_convolution_bound (I J : Finset ℤ) (a b : ℤ → ℝ)
    (ha : ∀ i∈I, 0≤a i) (hb : ∀ j∈J, 0≤b j) :
    (∑ i∈I, ∑ j∈J, measureClassKernel (i-j)*a i*b j)≤
      (∑' k, measureClassKernel k)*Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2) := by
  apply finite_schur_bound I J (fun i j => measureClassKernel (i-j)) a b _
    (tsum_nonneg measureClassKernel_nonneg) (fun i _ j _ => measureClassKernel_nonneg (i-j)) ha hb
  · intro i _
    have he (j : ℤ) : measureClassKernel (i-j)=measureClassKernel (j-i) := by
      rw [show i-j=-(j-i) by omega,measureClassKernel_neg]
    simp_rw [he]
    exact measureClassKernel_shift_sum_le J i
  · intro j _
    exact measureClassKernel_shift_sum_le I j

end LipschitzHilbert

end

end OAI

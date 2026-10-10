import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Supply
open MeasureTheory Set
open scoped Topology ContDiff

def primeBump : ContDiffBump (3/4:ℝ) := ⟨1/16,1/8,by norm_num,by norm_num⟩
def primeWeight : ℝ→ℝ := primeBump

theorem primeWeight_contDiff : ContDiff ℝ ∞ primeWeight := primeBump.contDiff
theorem primeWeight_nonneg (x : ℝ) : 0≤primeWeight x := primeBump.nonneg
theorem primeWeight_le_one (x : ℝ) : primeWeight x≤1 := primeBump.le_one
theorem primeWeight_compact : HasCompactSupport primeWeight := primeBump.hasCompactSupport

theorem primeWeight_support : tsupport primeWeight ⊆ Ioo (1/2:ℝ) 1 := by
  rw [primeWeight,primeBump.tsupport_eq]
  intro x hx
  change dist x (3/4:ℝ)≤(1/8:ℝ) at hx
  rw [Real.dist_eq] at hx
  obtain ⟨ha,hb⟩ := abs_le.mp hx
  constructor <;> linarith

theorem primeWeight_integral_pos : 0<∫x in Ioi (0:ℝ),primeWeight x := by
  have he : (∫x in Ioi (0:ℝ),primeWeight x) = ∫x,primeWeight x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_contra hh
    have hm : x∈tsupport primeWeight := subset_closure hh
    have hp := (primeWeight_support hm).1
    exact hx (by change 0<x; linarith)
  rw [he]
  exact primeBump.integral_pos

end Ostmann.Supply

end

end OAI

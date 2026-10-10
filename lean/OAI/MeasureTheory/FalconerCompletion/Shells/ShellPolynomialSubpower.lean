import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SharedBinSupportCollision

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Filter Asymptotics
open scoped Topology
theorem shell_polynomial_subpowerND (k : ℕ) (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, C*(N:ℝ)^k ≤ ((2:ℝ)^N)^ε := by
  have hr : 1<(2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hr).const_mul C
  have hh : ∀ᶠ N : ℕ in atTop, C*((N:ℝ)^k/((2:ℝ)^ε)^N) ≤ 1 := by
    have hc := ht.eventually_lt_const (show C*0 < (1:ℝ) by simp)
    exact hc.mono (fun _ h => h.le)
  filter_upwards [hh] with N hN
  have he : ((2:ℝ)^ε)^N=((2:ℝ)^N)^ε := by
    rw [← Real.rpow_natCast ((2:ℝ)^ε) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2),
      ← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2),mul_comm ε]
  rw [← mul_div_assoc] at hN
  exact ((div_le_one (by positivity)).mp hN).trans_eq he

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI

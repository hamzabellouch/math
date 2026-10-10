import OAI.NumberTheory.Ostmann.Preliminaries.PrimeLogReciprocal
import OAI.NumberTheory.Ostmann.Supply.ResidueBudgetScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Preliminaries
open scoped BigOperators

def actualLogBudget (d : Decomposition) (Q : ℕ) : ℝ :=
  ∑ p∈Q.primesLE, |Real.log (actualRatio d p)|/(p:ℝ)

theorem actualLogBudget_nonneg (d : Decomposition) (Q : ℕ) : 0 ≤ actualLogBudget d Q :=
  Finset.sum_nonneg (fun _p _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

theorem eventually_actualLogBudget_le (d : Decomposition) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Q : ℕ in atTop,
      actualLogBudget d Q ≤ C*Real.sqrt (Real.log (Real.log (Q:ℝ))) := by
  obtain ⟨C,hC,hweighted⟩ := eventually_ratioWeightedSum_le d
  obtain ⟨D,hD,hreciprocal⟩ := prime_log_reciprocal_sum_bounded
  refine ⟨Real.sqrt (C*D),Real.sqrt_pos.mpr (mul_pos hC hD),?_⟩
  have hx : Tendsto (fun Q : ℕ => (Q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hweighted,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hx)).eventually_ge_atTop 0]
    with Q hweighted hloglog
  change 0 ≤ Real.log (Real.log (Q:ℝ)) at hloglog
  have hsets : Q.primesLE = (Finset.Ioc 0 Q).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE,Finset.mem_filter,Finset.mem_Ioc]
    exact ⟨fun h => ⟨⟨h.2.pos,h.1⟩,h.2⟩,fun h => ⟨h.1.2,h.2⟩⟩
  have hrec : (∑ p∈Q.primesLE,1/((p:ℝ)*Real.log p)) ≤ D := by
    rw [hsets]
    exact hreciprocal Q
  have hs := logRatio_cauchy Q.primesLE (actualRatio d)
    (fun p hp => (Nat.mem_primesLE.mp hp).2)
    (fun p hp => actualRatio_pos d (Nat.mem_primesLE.mp hp).2)
  change (actualLogBudget d Q)^2 ≤ ratioWeightedSum d Q * _ at hs
  have hs' : (actualLogBudget d Q)^2 ≤ C*D*Real.log (Real.log (Q:ℝ)) := by
    calc
      _ ≤ ratioWeightedSum d Q*(∑ p∈Q.primesLE,1/((p:ℝ)*Real.log p)) := hs
      _ ≤ ratioWeightedSum d Q*D := mul_le_mul_of_nonneg_left hrec (ratioWeightedSum_nonneg d Q)
      _ ≤ (C*Real.log (Real.log (Q:ℝ)))*D := mul_le_mul_of_nonneg_right hweighted hD.le
      _ = _ := by ring
  have hsq1 := Real.sq_sqrt (mul_pos hC hD).le
  have hsq2 := Real.sq_sqrt hloglog
  have hnonneg : 0 ≤ Real.sqrt (C*D)*Real.sqrt (Real.log (Real.log (Q:ℝ))) := by positivity
  have he : (Real.sqrt (C*D)*Real.sqrt (Real.log (Real.log (Q:ℝ))))^2 =
      C*D*Real.log (Real.log (Q:ℝ)) := by rw [mul_pow,hsq1,hsq2]
  nlinarith [actualLogBudget_nonneg d Q]

end Ostmann.Supply

end

end OAI

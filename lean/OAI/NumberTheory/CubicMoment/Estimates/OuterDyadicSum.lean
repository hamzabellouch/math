import OAI.NumberTheory.DirichletL.CubicDyadicDecay
import OAI.NumberTheory.CubicMoment.Estimates.AllFrequencyOuterSieve

namespace OAI

/-! Summation of all three outer-sieve powers at the true Poisson scale. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
open SevenEighths.CubicDyadicDecay

lemma finite_dyadic_power_decay (I : Finset ℕ) {t α : ℝ}
    (ht : 0 < t) (hα : 0 < α) (hα3 : α < 3) :
    (∑ j ∈ I, ((2:ℝ)^j)^α/(1+t*2^j)^3) ≤ SevenEighths.CubicDyadicDecay.decayConstant α*t^(-α) := by
  exact ((decay_summable t α ht hα3).sum_le_tsum I (fun j _ => by positivity)).trans
    (dyadic_decay_bound t α ht hα hα3)

def outerDyadicBound (ε N t : ℝ) : ℝ :=
  SevenEighths.CubicDyadicDecay.decayConstant (ε+1)*t^(-(ε+1))+
  N^(2/3:ℝ)*SevenEighths.CubicDyadicDecay.decayConstant (ε+2/3)*t^(-(ε+2/3))+
  N*SevenEighths.CubicDyadicDecay.decayConstant (ε+1/3)*t^(-(ε+1/3))

lemma outerDyadicBound_pos {ε N t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hN : 0 < N) (ht : 0 < t) : 0 < outerDyadicBound ε N t := by
  have h1 := SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1) (by linarith) (by linarith)
  have h2 := SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+2/3) (by linarith) (by linarith)
  have h3 := SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1/3) (by linarith) (by linarith)
  unfold outerDyadicBound
  positivity

lemma sum_outer_dyadic_envelope (I : Finset ℕ) {ε N t : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 0 ≤ N) (ht : 0 < t) :
    (∑ j ∈ I, ((2:ℝ)^j)^ε *
      ((2:ℝ)^j+((2:ℝ)^j*N)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*N)/(1+t*2^j)^3) ≤
      outerDyadicBound ε N t := by
  have hp (j : ℕ) : ((2:ℝ)^j)^ε *
      ((2:ℝ)^j+((2:ℝ)^j*N)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*N)/(1+t*2^j)^3 =
      ((2:ℝ)^j)^(ε+1)/(1+t*2^j)^3+
      N^(2/3:ℝ)*(((2:ℝ)^j)^(ε+2/3)/(1+t*2^j)^3)+
      N*(((2:ℝ)^j)^(ε+1/3)/(1+t*2^j)^3) := by
    rw [Real.mul_rpow (by positivity) hN,Real.rpow_add (by positivity),
      Real.rpow_add (by positivity),Real.rpow_add (by positivity),Real.rpow_one]
    ring
  simp_rw [hp,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  simpa only [outerDyadicBound,mul_assoc] using add_le_add (add_le_add
    (finite_dyadic_power_decay (α := ε+1) I ht (by linarith) (by linarith))
    (mul_le_mul_of_nonneg_left (finite_dyadic_power_decay (α := ε+2/3) I ht (by linarith) (by linarith))
      (Real.rpow_nonneg hN _)))
    (mul_le_mul_of_nonneg_left (finite_dyadic_power_decay (α := ε+1/3) I ht (by linarith) (by linarith)) hN)

end CubicFirstMoment

end

end OAI

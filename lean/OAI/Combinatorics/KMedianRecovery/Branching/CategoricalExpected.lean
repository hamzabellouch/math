import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.GreedyOutputExpected

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

lemma categorical_expected {E : Type*} [Fintype E] [DecidableEq E]
    {a T L : ℕ} [NeZero T] (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {tau : ℝ} (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (hL : 0 < L)
    (hcount : (T:ℝ) * Fintype.card E * a^2 / (4*tau^3) ≤ L)
    (S : Finset E) (hS : PartitionFeasible part S) :
    (1 - 1/Real.exp 1 - 4*tau) * g S ≤
      average (fun seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T) =>
        g (greedyOutput part hp g seed)) := by
  have hnonneg : ∀ U, 0 ≤ g U := fun U => by
    rw [← hg0]
    exact hmono (Finset.empty_subset U)
  obtain ⟨e, _⟩ := hp ⟨0,ha⟩
  have hE : (Finset.univ : Finset E).Nonempty := ⟨e, Finset.mem_univ e⟩
  obtain ⟨emax, _, hmax⟩ := Finset.univ.exists_max_image (fun e : E => g {e}) hE
  have hbound := boundedMarginals_of_submodular g hmono hsub hg0
    (fun e => hmax e (Finset.mem_univ _))
  by_cases hM : 0 < g {emax}
  · obtain ⟨o, ho, hopt⟩ := exists_optimal_assignment part hp g hmono
    have havg := greedyOutput_expected part hp g o ho hmono hsub hg0 hM
      (hopt {emax} (partitionFeasible_singleton part emax)) hbound ha htau htau1
      hscale hL hcount
    have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hehalf : 1/Real.exp 1 ≤ (1:ℝ)/2 := by
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      linarith
    exact (mul_le_mul_of_nonneg_left (hopt S hS) (by linarith)).trans havg
  · have hM0 : g {emax} = 0 := le_antisymm (not_lt.mp hM) (hnonneg _)
    rw [hM0] at hbound
    rw [zero_of_boundedMarginals_zero g hg0 hbound S, mul_zero]
    exact average_nonneg (fun _ => hnonneg _)

end MetricKMedianRecovery.Categorical

end OAI

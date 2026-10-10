import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! A finite Euler product retains at least half its mass below a cutoff
whenever its logarithmic moment is at most half that cutoff. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma sieve_euler_log_moment {ι : Type*} (S : Finset ι) (g ℓ : ι → ℝ)
    (hg : ∀ p ∈ S, 0 ≤ g p) :
    (∑ T ∈ S.powerset, (∏ p ∈ T, g p) * (∑ p ∈ T, ℓ p)) =
      (∏ p ∈ S, (1 + g p)) * (∑ p ∈ S, g p / (1 + g p) * ℓ p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hga : 0 ≤ g a := hg a (mem_insert_self _ _)
    have hgS : ∀ p ∈ S, 0 ≤ g p := fun p hp => hg p (mem_insert_of_mem hp)
    have hne : 1 + g a ≠ 0 := by positivity
    have hn (T : Finset ι) (hT : T ∈ S.powerset) : a ∉ T :=
      fun h => ha ((mem_powerset.mp hT) h)
    have hins :
        (∑ T ∈ S.powerset, (∏ p ∈ insert a T, g p) * (∑ p ∈ insert a T, ℓ p)) =
          g a * ℓ a * (∏ p ∈ S, (1 + g p)) +
            g a * ((∏ p ∈ S, (1 + g p)) * (∑ p ∈ S, g p / (1 + g p) * ℓ p)) := by
      calc
        _ = ∑ T ∈ S.powerset,
            (g a * ℓ a * (∏ p ∈ T, g p) + g a * ((∏ p ∈ T, g p) * (∑ p ∈ T, ℓ p))) := by
          apply sum_congr rfl
          intro T hT
          rw [prod_insert (hn T hT), sum_insert (hn T hT)]
          ring
        _ = _ := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← prod_one_add, ih hgS]
    rw [sum_powerset_insert ha, hins, ih hgS, prod_insert ha, sum_insert ha]
    field_simp
    ring

lemma sieve_euler_truncation {ι : Type*} (S : Finset ι) (g ℓ : ι → ℝ)
    (hg : ∀ p ∈ S, 0 ≤ g p) (hℓ : ∀ p ∈ S, 0 ≤ ℓ p)
    {L : ℝ} (hL : 0 < L)
    (hmean : (∑ p ∈ S, g p / (1 + g p) * ℓ p) ≤ L / 2) :
    (∏ p ∈ S, (1 + g p)) / 2 ≤
      ∑ T ∈ S.powerset with (∑ p ∈ T, ℓ p) ≤ L, ∏ p ∈ T, g p := by
  classical
  let Z := ∏ p ∈ S, (1 + g p)
  have hZ : 0 ≤ Z := prod_nonneg (fun p hp => by linarith [hg p hp])
  have hweight (T : Finset ι) (hT : T ∈ S.powerset) : 0 ≤ ∏ p ∈ T, g p :=
    prod_nonneg (fun p hp => hg p (mem_powerset.mp hT hp))
  have hcost (T : Finset ι) (hT : T ∈ S.powerset) : 0 ≤ ∑ p ∈ T, ℓ p :=
    sum_nonneg (fun p hp => hℓ p (mem_powerset.mp hT hp))
  have htail :
      L * (∑ T ∈ S.powerset with ¬ (∑ p ∈ T, ℓ p) ≤ L, ∏ p ∈ T, g p) ≤
        ∑ T ∈ S.powerset, (∏ p ∈ T, g p) * (∑ p ∈ T, ℓ p) := by
    rw [sum_filter, mul_sum]
    apply sum_le_sum
    intro T hT
    split_ifs with h
    · simpa using mul_nonneg (hweight T hT) (hcost T hT)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (hweight T hT)
  rw [sieve_euler_log_moment S g ℓ hg] at htail
  have hm := mul_le_mul_of_nonneg_left hmean hZ
  have htotal := sum_filter_add_sum_filter_not S.powerset
    (fun T => (∑ p ∈ T, ℓ p) ≤ L) (fun T => ∏ p ∈ T, g p)
  rw [← prod_one_add] at htotal
  dsimp [Z] at hZ hm
  nlinarith

end TwoPointCorrelations

end OAI

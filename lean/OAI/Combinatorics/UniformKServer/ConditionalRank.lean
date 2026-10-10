import Mathlib
import OAI.Combinatorics.UniformKServer.RankTracking

namespace OAI

                                      
section

/-! Source §02/§03: the rank-tracker input is constructed from a hidden count,
 not obtained by assuming a martingale. Summed posterior rank drift is bounded
 by the actual count drift, with coefficient one. -/
namespace UniformKServer.ConditionalRank
noncomputable section
open Finset ConditionalLaw
variable {Ω : Type*} [Fintype Ω]

def indicator (n j : ℕ) : ℝ := if n ≤ j then 1 else 0

theorem indicator_range (n j : ℕ) : indicator n j ∈ Set.Icc (0:ℝ) 1 := by
  unfold indicator
  split_ifs <;> norm_num

theorem indicator_sum {n k : ℕ} (hn : n ≤ k) :
    (∑ j ∈ range k, indicator n j) = (k:ℝ)-n := by
  induction k with
  | zero =>
    have : n=0 := by omega
    subst n
    simp
  | succ k ih =>
    by_cases hk : n ≤ k
    · rw [sum_range_succ,ih hk,indicator,ite_eq_left hk,Nat.cast_succ]
      ring
    · have he : n=k+1 := by omega
      subst n
      have hz : (∑ j ∈ range k, indicator (k+1) j) = 0 := by
        apply sum_eq_zero
        intro j hj
        have hj' := mem_range.mp hj
        simp only [indicator,ite_eq_right (by omega : ¬k+1 ≤ j)]
      rw [sum_range_succ,hz]
      simp only [indicator,ite_eq_right (by omega : ¬k+1 ≤ k),Nat.cast_add,Nat.cast_one]
      ring

theorem indicator_distance_ordered {n m k : ℕ} (hnm : n ≤ m) (hm : m ≤ k) :
    (∑ j ∈ range k, |indicator n j-indicator m j|) = (m:ℝ)-n := by
  have he (j : ℕ) : |indicator n j-indicator m j| = indicator n j-indicator m j := by
    apply abs_of_nonneg
    unfold indicator
    split_ifs <;> norm_num at *
    omega
  simp_rw [he]
  rw [sum_sub_distrib,indicator_sum (hnm.trans hm),indicator_sum hm]
  ring

theorem indicator_distance {n m k : ℕ} (hn : n ≤ k) (hm : m ≤ k) :
    (∑ j ∈ range k, |indicator n j-indicator m j|) = |(n:ℝ)-m| := by
  rcases le_total n m with h|h
  · rw [indicator_distance_ordered h hm,abs_of_nonpos (by exact_mod_cast (show (n:ℤ)-m ≤ 0 by omega))]
    ring
  · simp_rw [abs_sub_comm (indicator n _) (indicator m _)]
    rw [indicator_distance_ordered h hn,abs_of_nonneg (by exact_mod_cast (show (0:ℤ) ≤ (n:ℤ)-m by omega))]

/-- Actual finite posterior input for each child rank. -/
def input (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (htotal : ∑ ω, w ω=1)
    (F : ℕ → Setoid Ω) (hF : ∀ t ω v, (F (t+1)).r ω v → (F t).r ω v)
    (N : ℕ → Ω → ℕ) (j : ℕ) : RankTracking.Input Ω where
  weight := w
  weight_nonneg := hw
  weight_total := htotal
  filtration := F
  refines := hF
  posterior t := posterior w (F t) (fun ω => indicator (N t ω) j)
  filtered t := posterior w (F t) (fun ω => indicator (N (t-1) ω) j)
  posterior_range t ω := ⟨posterior_nonneg hw (fun v => (indicator_range (N t v) j).1) (F t) ω,
    posterior_le_one hw (fun v => (indicator_range (N t v) j).2) (F t) ω⟩
  filtered_range t ω := ⟨posterior_nonneg hw (fun v => (indicator_range (N (t-1) v) j).1) (F t) ω,
    posterior_le_one hw (fun v => (indicator_range (N (t-1) v) j).2) (F t) ω⟩
  posterior_measurable t := posterior_measurable w (F t) _
  filtering t a ha := by
    simp only [Nat.add_sub_cancel,RankTracking.average]
    have h := filtering hw (F t) (F (t+1)) (hF t) a (fun ω => indicator (N t ω) j) ha
    simpa only [mul_assoc] using h

theorem total_drift {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (N M : Ω → ℕ) (k : ℕ) (hN : ∀ ω, N ω ≤ k) (hM : ∀ ω, M ω ≤ k) :
    (∑ j ∈ range k, ∑ ω, w ω *
      |posterior w F (fun v => indicator (N v) j) ω-
       posterior w F (fun v => indicator (M v) j) ω|) ≤
      ∑ ω, w ω*|(N ω:ℝ)-M ω| := by
  calc
    _ ≤ ∑ j ∈ range k, ∑ ω, w ω*|indicator (N ω) j-indicator (M ω) j| := by
      apply sum_le_sum
      intro j _
      exact expected_contraction hw F _ _
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro ω _
      rw [←mul_sum,indicator_distance (hN ω) (hM ω)]

end
end UniformKServer.ConditionalRank

end

end OAI

import OAI.Probability.SATComputability.DeletionMean
import OAI.Probability.SATComputability.DyadicBlocks

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory
open scoped BigOperators

theorem sixth_fifth_power_le_sum (d : ℕ) :
    (d : ℝ)^(6/5 : ℝ) ≤
      (6/5 : ℝ) * ∑ j ∈ Finset.range d, ((j : ℝ)+1)^(1/5 : ℝ) := by
  have hm : MonotoneOn (fun x : ℝ => x^(1/5 : ℝ)) (Set.Icc 0 (0+(d : ℝ))) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow hx.1 hxy (by norm_num)
  have h := hm.integral_le_sum
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at h
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1/5))] at h
  norm_num at h
  nlinarith

theorem finite_fractional_moment {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    P.expect (fun ω => (f ω)^(1/5 : ℝ)) ≤ (P.expect f)^(1/5 : ℝ) := by
  exact (Real.concaveOn_rpow (by norm_num : (0 : ℝ) ≤ 1/5)
    (by norm_num : (1/5 : ℝ) ≤ 1)).le_map_sum
      (fun ω _ => P.nonneg ω) P.total (fun ω _ => hf ω)

theorem reverse_interval_sum (A B : ℕ) (hAB : A ≤ B) (f : ℕ → ℝ) :
    (∑ t ∈ Finset.Ico A B, f (B-t)) =
      ∑ j ∈ Finset.range (B-A), f (j+1) := by
  rw [Finset.sum_Ico_eq_sum_range, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hj' := Finset.mem_range.mp hj
  omega

theorem discrete_delay_moment {A B M : ℕ} (hAB : A ≤ B) (hBM : B ≤ M) :
    ((B-A : ℕ) : ℝ)^(6/5 : ℝ) ≤ (6/5 : ℝ) *
      ∑ t ∈ Finset.range M,
        if A ≤ t ∧ t < B then ((B-t : ℕ) : ℝ)^(1/5 : ℝ) else 0 := by
  have he : (∑ t ∈ Finset.range M,
      if A ≤ t ∧ t < B then ((B-t : ℕ) : ℝ)^(1/5 : ℝ) else 0) =
      ∑ t ∈ Finset.Ico A B, ((B-t : ℕ) : ℝ)^(1/5 : ℝ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he, reverse_interval_sum A B hAB (fun j => (j : ℝ)^(1/5 : ℝ))]
  simpa only [Nat.cast_add, Nat.cast_one] using sixth_fifth_power_le_sum (B-A)

end FixedClauseThreshold.Computability

end OAI

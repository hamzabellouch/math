import OAI.Probability.SATComputability.DeletionIncrement

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory
open scoped BigOperators

theorem sum_inverse_five_sixths (r : ℕ) :
    (∑ j ∈ Finset.range r, ((j : ℝ)+1)^(-(5/6 : ℝ))) ≤
      6 * (r : ℝ)^(1/6 : ℝ) := by
  have ha : AntitoneOn (fun x : ℝ => x^(-(5/6 : ℝ))) (Set.Ioc 0 (r : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (by norm_num)
  have hi : IntervalIntegrable (fun x : ℝ => x^(-(5/6 : ℝ))) volume 0 (r : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hfi : IntegrableOn (fun x : ℝ => x^(-(5/6 : ℝ))) (Set.Icc 0 (r : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (Nat.cast_nonneg r) (by simp)).mp hi
  have hb := (show AntitoneOn (fun x : ℝ => x^(-(5/6 : ℝ)))
      (Set.Ioc 0 (0+(r : ℝ))) by simpa using ha).sum_le_integral_of_integrableOn
    (by simpa using hfi)
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at hb
  apply hb.trans_eq
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(5/6 : ℝ)))]
  norm_num
  ring

theorem finite_deletion_mean {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    {n r : ℕ} (t : Ω → Finset (Fin n) → ℝ) (ht : ∀ ω, Monotone (t ω))
    {C : ℝ} (hC : 0 ≤ C)
    (hmoment : ∀ j < r, ∀ v : Fin n, P.expect (fun ω =>
      (freeDeletionTime (t ω) j v - bestDeletionTime (t ω) j)^(6/5 : ℝ)) ≤ C) :
    P.expect (fun ω => bestDeletionTime (t ω) r) -
        P.expect (fun ω => bestDeletionTime (t ω) 0) ≤
      6 * ((n : ℝ)*C)^(5/6 : ℝ) * (r : ℝ)^(1/6 : ℝ) := by
  let A := fun j => P.expect (fun ω => bestDeletionTime (t ω) j)
  have hnc : 0 ≤ (n : ℝ)*C := mul_nonneg (Nat.cast_nonneg _) hC
  have hj (j : ℕ) (hj : j < r) :
      A (j+1) - A j ≤ ((n : ℝ)*C)^(5/6 : ℝ) *
        ((j : ℝ)+1)^(-(5/6 : ℝ)) := by
    have h := mean_deletion_increment P t ht (Nat.succ_pos j)
      (by norm_num : (1 : ℝ) ≤ 6/5) (by
        simpa only [Nat.succ_sub_one] using hmoment j hj)
    simp only [Nat.succ_sub_one, Nat.cast_succ, one_div, FiniteLaw.expect_sub] at h
    norm_num only [inv_div, div_one] at h
    apply h.trans_eq
    rw [Real.div_rpow hnc (by positivity), div_eq_mul_inv,
      ← Real.rpow_neg (by positivity)]
  change A r - A 0 ≤ _
  calc
    _ = ∑ j ∈ Finset.range r, (A (j+1)-A j) := (Finset.sum_range_sub A r).symm
    _ ≤ ∑ j ∈ Finset.range r, ((n : ℝ)*C)^(5/6 : ℝ) *
        ((j : ℝ)+1)^(-(5/6 : ℝ)) :=
      Finset.sum_le_sum (fun j hj' => hj j (Finset.mem_range.mp hj'))
    _ = ((n : ℝ)*C)^(5/6 : ℝ) *
        ∑ j ∈ Finset.range r, ((j : ℝ)+1)^(-(5/6 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ ((n : ℝ)*C)^(5/6 : ℝ) * (6*(r : ℝ)^(1/6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inverse_five_sixths r) (Real.rpow_nonneg hnc _)
    _ = _ := by ring

end FixedClauseThreshold.Computability

end OAI

import OAI.Probability.SignedSweeps.PairTwirlLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma filter_range_antitone (r : ℕ → ℕ) (hr : Antitone r) (q t : ℕ) :
    ∃ k ≤ q, (Finset.range q).filter (fun i => t < r i) = Finset.range k := by
  induction q with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ q ih =>
    by_cases ht : t < r q
    · refine ⟨q+1, le_rfl, Finset.filter_eq_self.mpr ?_⟩
      intro i hi
      exact ht.trans_le (hr (by have := Finset.mem_range.mp hi; omega))
    · obtain ⟨k, hk, he⟩ := ih
      exact ⟨k, hk.trans (Nat.le_succ q), by simp only [Finset.range_add_one, Finset.filter_insert, ht, ite_false, he]⟩

lemma prefix_dominance_excess (r a : ℕ → ℕ) (q : ℕ) (hr : Antitone r)
    (h : ∀ k ≤ q, ∑ i ∈ Finset.range k, r i ≤ ∑ i ∈ Finset.range k, a i)
    (t : ℕ) :
    ∑ i ∈ Finset.range q, (r i - t) ≤ ∑ i ∈ Finset.range q, (a i - t) := by
  obtain ⟨k, hk, he⟩ := filter_range_antitone r hr q t
  have hs : ∑ i ∈ Finset.range q, (r i-t) = ∑ i ∈ Finset.range k, (r i-t) := by
    rw [← he, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with ht
    · rfl
    · exact Nat.sub_eq_zero_of_le (Nat.le_of_not_gt ht)
  have hrk : ∑ i ∈ Finset.range k, r i =
      (∑ i ∈ Finset.range k, (r i - t)) + k * t := by
    have hc : ∑ _i ∈ Finset.range k, t = k * t := by simp
    rw [← hc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ∈ (Finset.range q).filter (fun j => t < r j) := he.symm ▸ hi
    have ht : t < r i := (Finset.mem_filter.mp hi').2
    omega
  have hak : ∑ i ∈ Finset.range k, a i ≤
      (∑ i ∈ Finset.range k, (a i - t)) + k * t := by
    have hc : ∑ _i ∈ Finset.range k, t = k * t := by simp
    rw [← hc, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => by omega)
  have heq := h k hk
  rw [hrk] at heq
  have hkq : ∑ i ∈ Finset.range k, (a i-t) ≤ ∑ i ∈ Finset.range q, (a i-t) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun _ _ _ => Nat.zero_le _)
  rw [hs]
  omega

lemma log_factorial_ramp (n M : ℕ) (hM : n ≤ M) :
    Real.log (n.factorial : ℝ) =
      ∑ t ∈ Finset.range M, ((n-t : ℕ) : ℝ) * (Real.log (t+1 : ℕ) - Real.log t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnM : n ≤ M := by omega
    have he (t : ℕ) : ((n+1-t : ℕ) : ℝ) =
        ((n-t : ℕ) : ℝ) + if t ≤ n then 1 else 0 := by
      by_cases ht : t ≤ n
      · rw [ite_eq_left ht, show n+1-t = (n-t)+1 by omega, Nat.cast_add, Nat.cast_one]
      · rw [ite_eq_right ht, show n+1-t = 0 by omega, show n-t = 0 by omega]
        simp
    simp_rw [he, add_mul]
    rw [Finset.sum_add_distrib, ← ih hnM, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    have ht : (∑ t ∈ Finset.range M, (if t ≤ n then (1:ℝ) else 0) *
        (Real.log (t+1 : ℕ) - Real.log t)) = Real.log (n+1 : ℕ) := by
      calc
        _ = ∑ t ∈ Finset.range (n+1), (Real.log (t+1 : ℕ) - Real.log t) := by
          simp only [ite_mul, one_mul, zero_mul]
          rw [← Finset.sum_filter]
          have hs : (Finset.range M).filter (fun t => t ≤ n) = Finset.range (n+1) := by
            ext t
            simp only [Finset.mem_filter, Finset.mem_range]
            omega
          simpa only [ite_mul, one_mul, zero_mul] using congrArg
            (fun S : Finset ℕ => ∑ t ∈ S, (Real.log (t+1 : ℕ) - Real.log t)) hs
        _ = _ := by simpa only [Nat.cast_zero, Real.log_zero, sub_zero] using
          Finset.sum_range_sub (fun t : ℕ => Real.log (t : ℝ)) (n+1)
    rw [ht]
    ring

theorem factorial_product_le_of_prefix_dominance (r a : ℕ → ℕ) (q : ℕ)
    (hr : Antitone r)
    (h : ∀ k ≤ q, ∑ i ∈ Finset.range k, r i ≤ ∑ i ∈ Finset.range k, a i) :
    ∏ i ∈ Finset.range q, (r i).factorial ≤ ∏ i ∈ Finset.range q, (a i).factorial := by
  let M := ∑ i ∈ Finset.range q, (r i + a i)
  have hrM (i : ℕ) (hi : i ∈ Finset.range q) : r i ≤ M :=
    (Nat.le_add_right (r i) (a i)).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (r j+a j)) hi)
  have haM (i : ℕ) (hi : i ∈ Finset.range q) : a i ≤ M :=
    (Nat.le_add_left (a i) (r i)).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (r j+a j)) hi)
  suffices hh : Real.log ((∏ i ∈ Finset.range q, (r i).factorial : ℕ) : ℝ) ≤
      Real.log ((∏ i ∈ Finset.range q, (a i).factorial : ℕ) : ℝ) by
    exact_mod_cast (Real.log_le_log_iff (by positivity) (by positivity)).mp hh
  rw [Nat.cast_prod, Nat.cast_prod, Real.log_prod (fun _ _ => by positivity),
    Real.log_prod (fun _ _ => by positivity)]
  have heR := Finset.sum_congr rfl (fun i hi => log_factorial_ramp (r i) M (hrM i hi))
  have heA := Finset.sum_congr rfl (fun i hi => log_factorial_ramp (a i) M (haM i hi))
  rw [heR, heA, Finset.sum_comm, Finset.sum_comm (s := Finset.range q)]
  apply Finset.sum_le_sum
  intro t ht
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast prefix_dominance_excess r a q hr h t
  · by_cases ht0 : t = 0
    · simp [ht0]
    · apply sub_nonneg.mpr
      exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ht0)
        (by exact_mod_cast Nat.le_succ t)

end SignedSweeps
end

end OAI

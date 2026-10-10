import OAI.NumberTheory.TotientAsymptotic.CofactorShellDecay

namespace OAI

/-! Summing the concentration loss over all retained prefix coordinates. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

theorem sum_retained_concentration {x c : ℝ} {H : ℕ} (hc : 0 < c)
    (hHm : H ≤ m x) (hPH : 2*P H ≤ H) :
    (∑ i : Fin (R x H), Real.exp (-c*((L x H-(i.val+1) : ℕ) : ℝ))) ≤
      (Real.exp (-c/2))^H/(1-Real.exp (-c/2)) := by
  let q := Real.exp (-c/2)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by dsimp [q]; rw [Real.exp_lt_one_iff]; linarith
  have hterm (i : Fin (R x H)) :
      Real.exp (-c*((L x H-(i.val+1) : ℕ) : ℝ)) ≤ q^(m x-(i.val+1)) := by
    have hi : i.val+1 ≤ m x-H := by have := i.isLt; unfold R at *; omega
    have hP : P H ≤ m x-(i.val+1) := by omega
    have hhalf : ((m x-(i.val+1) : ℕ) : ℝ) ≤
        2*((L x H-(i.val+1) : ℕ) : ℝ) := by
      have hn : m x-(i.val+1) ≤ 2*(L x H-(i.val+1)) := by unfold L; omega
      exact_mod_cast hn
    change Real.exp _ ≤ (Real.exp (-c/2))^_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  apply (Finset.sum_le_sum (fun i _ => hterm i)).trans
  change (∑ i : Fin (m x-H), q^(m x-(i.val+1))) ≤ _
  rw [sum_reverse_prefix hHm (fun h => q^h)]
  have hg : Summable (fun n : ℕ => q^n) := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑' n : ℕ, q^(H+n) := (hg.comp_injective (fun _ _ h => by omega)).sum_le_tsum
      _ (fun _ _ => pow_nonneg hq0 _)
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      rfl

lemma cofactor_concentration_tail_tendsto (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℕ => Real.exp (C*cofactorScale H)*
      (Real.exp (-c/2))^H/(1-Real.exp (-c/2))) atTop (nhds 0) := by
  have hq0 : 0 ≤ Real.exp (-c/2) := (Real.exp_pos _).le
  have hq1 : Real.exp (-c/2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have ht := cofactor_polynomialGeometricTail_tendsto C 0 hq0 hq1
  have he (H : ℕ) : polynomialGeometricTail 0 (Real.exp (-c/2)) H =
      (Real.exp (-c/2))^H/(1-Real.exp (-c/2)) := by
    unfold polynomialGeometricTail
    simp only [pow_zero, one_mul, pow_add]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    rfl
  simp_rw [he] at ht
  simpa only [mul_div_assoc] using ht

end TotientAsymptotic

end

end OAI

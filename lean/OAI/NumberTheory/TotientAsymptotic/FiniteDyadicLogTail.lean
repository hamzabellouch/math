import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicQuadratic

namespace OAI

/-! Finite partial summation for logarithmic sieve bounds. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_dyadic_log_range (Q : Finset ℕ) (hQ : Q.Nonempty)
    {U : ℝ} (hU : 1 < U) (hlo : ∀ q ∈ Q,U ≤ q) :
    ∃ K L : ℕ, 1 ≤ K ∧ Real.log U ≤ (K:ℝ)*Real.log 2 ∧
      (∀ q ∈ Q,Nat.clog 2 q ∈ Finset.Icc K L) ∧
      (∀ q ∈ Q,(2:ℝ)^(Nat.clog 2 q)/4 ≤ q) := by
  classical
  let T := Q.image (Nat.clog 2)
  have hT : T.Nonempty := hQ.image _
  let K := T.min' hT
  obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
  have hq1 : 1 < q := by exact_mod_cast (hU.trans_le (hlo q hq))
  have hb := dyadic_nat_bounds hq1
  rw [heq] at hb
  refine ⟨K,Q.sup (Nat.clog 2),hb.1,?_,?_,?_⟩
  · calc
      Real.log U ≤ Real.log (q:ℝ) := Real.log_le_log (zero_lt_one.trans hU) (hlo q hq)
      _ ≤ Real.log ((2:ℝ)^K) := Real.log_le_log (by exact_mod_cast (show 0 < q by omega)) hb.2.2
      _ = _ := dyadic_endpoint_log K
  · intro q hq
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le T _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩),
      Finset.le_sup hq⟩
  · intro q hq
    have hq1 : 1 < q := by exact_mod_cast (hU.trans_le (hlo q hq))
    have hh := (dyadic_nat_bounds hq1).2.1
    have hp : 0 < (2:ℝ)^(Nat.clog 2 q) := by positivity
    linarith

lemma finite_dyadic_log_square_tail (Q : Finset ℕ) {U A : ℝ}
    (hU : 1 < U) (hA : 0 ≤ A) (hlo : ∀ q ∈ Q,U ≤ q)
    (hc : ∀ k : ℕ,1 ≤ k → ((Q.filter (fun q => Nat.clog 2 q=k)).card:ℝ) ≤
      A*(2:ℝ)^k/(k:ℝ)^2) :
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ 8*A*Real.log 2/Real.log U := by
  classical
  by_cases hQ : Q.Nonempty
  · obtain ⟨K,L,hK,hlog,hn,hv⟩ := finite_dyadic_log_range Q hQ hU hlo
    have hh := finite_dyadic_quadratic_mass Q (Nat.clog 2) (fun q => (q:ℝ))
      K L hK hA hn hv (fun k hk => hc k (hK.trans (Finset.mem_Icc.mp hk).1))
    have hK0 : (0:ℝ) < K := by exact_mod_cast hK
    have hLU : 0 < Real.log U := Real.log_pos hU
    apply hh.trans
    apply (div_le_div_iff₀ hK0 hLU).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8*A by positivity)]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp only [Finset.sum_empty]
    have hLU : 0 < Real.log U := Real.log_pos hU
    have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity

lemma finite_dyadic_log_cube_tail (Q : Finset ℕ) {U A : ℝ}
    (hU : 1 < U) (hA : 0 ≤ A) (hlo : ∀ q ∈ Q,U ≤ q)
    (hc : ∀ k : ℕ,1 ≤ k → ((Q.filter (fun q => Nat.clog 2 q=k)).card:ℝ) ≤
      A*(2:ℝ)^k/(k:ℝ)^3) :
    (∑ q ∈ Q,(q:ℝ)⁻¹) ≤ 8*A*(Real.log 2)^2/(Real.log U)^2 := by
  classical
  by_cases hQ : Q.Nonempty
  · obtain ⟨K,L,hK,hlog,hn,hv⟩ := finite_dyadic_log_range Q hQ hU hlo
    have hh := finite_dyadic_cubic_mass Q (Nat.clog 2) (fun q => (q:ℝ))
      K L hK hA hn hv (fun k hk => hc k (hK.trans (Finset.mem_Icc.mp hk).1))
    have hK0 : (0:ℝ) < K := by exact_mod_cast hK
    have hLU : 0 < Real.log U := Real.log_pos hU
    have hs := pow_le_pow_left₀ hLU.le hlog 2
    apply hh.trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hK0) (sq_pos_of_pos hLU)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 8*A by positivity)]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp only [Finset.sum_empty]
    have hLU : 0 < Real.log U := Real.log_pos hU
    have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity

end TotientAsymptotic

end

end OAI

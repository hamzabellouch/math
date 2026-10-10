import OAI.Analysis.Triangular.Certificate.WaveIntervals

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Envelope

lemma factorial_term_step {d r : ℝ} {k : ℕ} (hd : 0 ≤ d) (hdr : d ≤ r*(k+1)) :
    d^(k+1)/(k+1).factorial  ≤  r*(d^k/k.factorial) := by
  have hk : (0:ℝ)<k+1 := by positivity
  have hf : (0:ℝ)<k.factorial := by positivity
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  apply (div_le_iff₀ (mul_pos hk hf)).mpr
  have hh := mul_le_mul_of_nonneg_left hdr (pow_nonneg hd k)
  convert hh using 1
  field_simp
lemma factorial_tail_geometric {d r : ℝ} (N : ℕ) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hdr : d ≤ r*(N+1)) (i : ℕ) :
    d^(i+N)/(i+N).factorial  ≤  (d^N/N.factorial)*r^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hni : (N:ℝ)+1 ≤ (i+N:ℕ)+1 := by exact_mod_cast (show N+1 ≤ i+N+1 by omega)
    have hs := factorial_term_step (k:=i+N) hd (hdr.trans (mul_le_mul_of_nonneg_left hni hr))
    calc
      d^(i+1+N)/(i+1+N).factorial = d^(i+N+1)/(i+N+1).factorial := by rw [show i+1+N=i+N+1 by omega]
      _  ≤  r*(d^(i+N)/(i+N).factorial) := hs
      _  ≤  r*((d^N/N.factorial)*r^i) := mul_le_mul_of_nonneg_left ih hr
      _ = _ := by rw [pow_succ]; ring
lemma exp_tail_bound {d r : ℝ} (N : ℕ) (hd : 0 ≤ d) (hr : 0 ≤ r) (hr1 : r<1)
    (hdr : d ≤ r*(N+1)) :
    Real.exp d-(∑ i ∈ Finset.range N, d^i/i.factorial)  ≤  (d^N/N.factorial)/(1-r) := by
  have hf := NormedSpace.expSeries_div_summable d
  have ht : ∑' i : ℕ, d^i/i.factorial = Real.exp d := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp d).tsum_eq
  have he := hf.sum_add_tsum_nat_add N
  rw [ht] at he
  have hh := Summable.tsum_le_tsum (factorial_tail_geometric N hd hr hdr)
    ((summable_nat_add_iff N).mpr hf) ((summable_geometric_of_lt_one hr hr1).mul_left (d^N/N.factorial))
  rw [tsum_mul_left,tsum_geometric_of_lt_one hr hr1] at hh
  rw [div_eq_mul_inv]
  linarith
lemma complex_exp_tail_bound (z : ℂ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    (hz : ‖z‖ ≤ r*(N+1)) :
    ‖Complex.exp z-∑ i ∈ Finset.range N, z^i/i.factorial‖  ≤ 
      (‖z‖^N/N.factorial)/(1-r) :=
  (Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z N).trans
    (exp_tail_bound N (norm_nonneg z) hr hr1 hz)
end AtomicTriangular.Envelope
end

end OAI

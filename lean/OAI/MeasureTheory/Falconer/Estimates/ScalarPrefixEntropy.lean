import OAI.MeasureTheory.Falconer.Estimates.ScalarPrefixNonconcentration

namespace OAI

/-! Entropy accounting for the ungrouped prefix. The lower estimate comes
 directly from the original finite set's ball bound. -/
namespace Falconer

 theorem scalar_dyadic_prefix_entropy {a W : ℕ} {K κ : ℝ} (hK : 0 < K)
    (h : 1 ≤ (2:ℝ)^W*K*((1/2:ℝ)^a)^κ) :
    κ*(a:ℝ)*Real.log 2 ≤ Real.log K+(W:ℝ)*Real.log 2 := by
  have hh := Real.log_le_log (by norm_num : (0:ℝ) < 1) h
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [Real.log_one,Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hK.ne',Real.log_pow,
    Real.log_rpow (by positivity),Real.log_pow,hhalf] at hh
  nlinarith

 theorem scalar_stopped_prefix_length {a W lo B P : ℕ} {K κ : ℝ}
    (hK : 0 < K) (hκ : 0 ≤ κ)
    (hcount : 1 ≤ (2:ℝ)^W*K*((1/2:ℝ)^a)^κ)
    (ha : B*lo ≤ a) (hW : (W:ℝ) ≤ 2*(P:ℝ)*(lo:ℝ)) :
    (κ*(B:ℝ)-2*(P:ℝ))*(lo:ℝ)*Real.log 2 ≤ Real.log K := by
  have hh := scalar_dyadic_prefix_entropy hK hcount
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have haR : (B:ℝ)*(lo:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hlow := mul_le_mul_of_nonneg_left haR (mul_nonneg hκ hlog)
  have hupp := mul_le_mul_of_nonneg_right hW hlog
  nlinarith

namespace Regularization

 theorem scalar_uniform_prefix_entropy {N M j : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k : ℕ → ℕ)
    (hd : Monotone d) (hd0 : d 0 = 0) (hdN : d j ≤ N) (hj : j ≤ M)
    (hcard : ∀ i < M, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i))
    {K κ : ℝ} (hK : 0 < K)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K*t^κ*((L.image scalarPathCenter).card:ℝ)) :
    κ*(d j:ℝ)*Real.log 2 ≤ Real.log K+(∑ i ∈ Finset.range j, (k i:ℝ))*Real.log 2 := by
  have hc := scalar_prefix_nonconcentration L hL hne hdN hball
  rw [scalar_uniform_prefix_card L hne d k hd hd0 hcard hj,Nat.cast_pow,Nat.cast_ofNat] at hc
  have he := scalar_dyadic_prefix_entropy hK hc
  simpa only [Nat.cast_sum] using he

end Regularization
end Falconer

end OAI

import OAI.Combinatorics.ParityLifts.UniformETH

namespace OAI

namespace ParityWL.Complexity

/-- Nonnegative exponents and positive multipliers in `UniformWLBound` are a
normalization, not an added restriction on uniform exclusion. -/
theorem uniform_eth_unrestricted_exponents (hETH : UniformSubexponentialETH)
    (c : Convention) (i : Implementation) :
    ¬ ∃ (M : Machine) (f g : ℕ → ℝ),
      Filter.Tendsto (fun k : ℕ => g k/k) Filter.atTop (nhds 0) ∧
      ∀ k : ℕ, 4 ≤ k → ∀ (n : ℕ) (G H : SimpleGraph (Fin n)), ∃ s b,
        Emits M (encodeNat k++encodeGraphs G H) s b ∧
        (b=true↔Equivalent G H c i k) ∧ (s : ℝ) ≤ f k*(n+1 : ℝ)^g k := by
  intro h
  obtain ⟨M,f,g,hlim,hm⟩ := h
  have hlim' : Filter.Tendsto (fun k : ℕ => |g k|/k) Filter.atTop (nhds 0) := by
    have hnat : ∀ k : ℕ, |(k : ℝ)|=k := fun k => abs_of_nonneg (Nat.cast_nonneg k)
    simpa only [abs_div,hnat,abs_zero] using hlim.abs
  apply uniform_eth hETH c i
  refine ⟨M,(fun k => |f k|+1),(fun k => |g k|),hlim',?_⟩
  refine ⟨by intro k; positivity,fun k => abs_nonneg (g k),?_⟩
  intro k hk n G H
  obtain ⟨s,b,hs,hb,ht⟩ := hm k hk n G H
  refine ⟨s,b,hs,hb,ht.trans ?_⟩
  have hn : (1 : ℝ) ≤ n+1 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
  calc
    f k*(n+1 : ℝ)^g k ≤ (|f k|+1)*(n+1 : ℝ)^g k :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self (f k)]) (Real.rpow_nonneg (by positivity) _)
    _ ≤ (|f k|+1)*(n+1 : ℝ)^|g k| :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (le_abs_self _)) (by positivity)

end ParityWL.Complexity

end OAI

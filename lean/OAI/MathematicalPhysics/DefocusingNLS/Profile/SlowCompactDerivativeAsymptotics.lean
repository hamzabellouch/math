import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowCompactAsymptotics
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowDerivativeAsymptotics

namespace OAI

/-! # Compact-parameter uniformity after fixed spatial differentiation -/

open Set Polynomial

namespace DefocusingNLS

theorem iteratedDeriv_regularizedSlowSolution_compact_remainder (k n m : ℕ) (Q : Set ℂ)
    (hQ : IsCompact Q) (hq : ∀ q ∈ Q, -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Q, ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖x ^ (q + k) * iteratedDeriv k (regularizedSlowSolution q m) x -
        ((-1 : ℂ) ^ k * (ascPochhammer ℂ k).eval q) *
          slowAsymptoticPolynomial (q + k) (m + k) n x‖ ≤ C / ‖x‖ ^ (n + 1) := by
  let Q' := (fun q : ℂ => q + k) '' Q
  have hQ' : IsCompact Q' := hQ.image (continuous_id.add continuous_const)
  have hq' : ∀ q ∈ Q', -1 < q.re := by
    rintro _ ⟨q, hqmem, rfl⟩
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [hq q hqmem, Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨A, hA, hb⟩ := regularizedSlowSolution_compact_allOrders_remainder n (m + k) Q' hQ' hq'
  let c : ℂ → ℂ := fun q => (-1 : ℂ) ^ k * (ascPochhammer ℂ k).eval q
  have hc : Continuous c := continuous_const.mul (ascPochhammer ℂ k).continuous
  obtain ⟨J, hJ⟩ := hQ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max J 0 * A, mul_nonneg (le_max_right _ _) hA, ?_⟩
  intro q hqmem x hx hn
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans_le hn).ne'
  rw [normalized_iteratedDeriv_regularizedSlowSolution k q m x (hq q hqmem) hx hx0,
    ← mul_sub, norm_mul]
  have hco : ‖c q‖ ≤ max J 0 := (hJ q hqmem).trans (le_max_left _ _)
  have hbo := hb (q + k) (mem_image_of_mem _ hqmem) x hx hn
  calc
    _ ≤ max J 0 * (A / ‖x‖ ^ (n + 1)) :=
      mul_le_mul hco hbo (norm_nonneg _) (le_max_right _ _)
    _ = _ := by ring

end DefocusingNLS

end OAI

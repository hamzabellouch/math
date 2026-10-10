import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowUniformAsymptoticBound

namespace OAI

/-! # Uniform all-order asymptotics on compact parameter sets -/

open Set

namespace DefocusingNLS

theorem continuous_slowAsymptoticJet (m n : ℕ) :
    Continuous (fun q : ℂ => slowAsymptoticJet q m n) := by
  induction n with
  | zero => simpa only [slowAsymptoticJet] using (continuous_const : Continuous (fun _ : ℂ => (1 : ℂ)))
  | succ n ih =>
      simp only [slowAsymptoticJet]
      exact (continuous_id.mul ((continuous_const.sub continuous_const).sub continuous_id)).mul
        (ih.comp (continuous_id.add continuous_const))

/-- The all-order remainder constant can be chosen uniformly on every compact
subset of the regularized parameter half-plane Re(q)>-1. -/
theorem regularizedSlowSolution_compact_allOrders_remainder (n m : ℕ) (Q : Set ℂ)
    (hQ : IsCompact Q) (hq : ∀ q ∈ Q, -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Q, ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖normalizedSlowSolution q m x - slowAsymptoticPolynomial q m n x‖ ≤
        C / ‖x‖ ^ (n + 1) := by
  let Q' := (fun q : ℂ => q + (n + 1 : ℕ)) '' Q
  have hQ' : IsCompact Q' := hQ.image (continuous_id.add continuous_const)
  have hq' : ∀ q ∈ Q', -1 < q.re := by
    rintro _ ⟨q, hqmem, rfl⟩
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [hq q hqmem, Nat.cast_nonneg (α := ℝ) (n + 1)]
  obtain ⟨A, hA, hbound⟩ := exists_compactifiedSlowSolution_compact_bound m Q' hQ' hq'
  obtain ⟨J, hJ⟩ := hQ.exists_bound_of_continuousOn (continuous_slowAsymptoticJet m (n + 1)).continuousOn
  let C := max J 0 * A
  have hC : 0 ≤ C := mul_nonneg (le_max_right _ _) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro q hqmem x hx hn
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans_le hn).ne'
  have hqval := hq q hqmem
  have hf := (contDiffOn_compactifiedSlowSolution (n + 1) q m x hqval hx hx0).mono
    (show Icc (0 : ℝ) 1 ⊆ Ici 0 from fun _ ht => ht.1)
  have hD : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (n + 1) (compactifiedSlowSolution q m x) (Icc 0 1) t‖ ≤
        C / ‖x‖ ^ (n + 1) := by
    intro t ht
    rw [iteratedDerivWithin_compactifiedSlowSolution (n + 1) q m x hqval hx hx0 ht,
      norm_mul, norm_div, norm_pow]
    have hjet : ‖slowAsymptoticJet q m (n + 1)‖ ≤ max J 0 :=
      (hJ q hqmem).trans (le_max_left _ _)
    have hb := hbound (q + (n + 1 : ℕ)) (mem_image_of_mem _ hqmem) x hx hn t ht
    calc
      _ ≤ (max J 0 / ‖x‖ ^ (n + 1)) * A := by gcongr
      _ = C / ‖x‖ ^ (n + 1) := by dsimp [C]; ring
  have ht := taylor_mean_remainder_bound (f := compactifiedSlowSolution q m x)
    (by norm_num : (0 : ℝ) ≤ 1) hf (show (1 : ℝ) ∈ Icc 0 1 from ⟨by norm_num, le_rfl⟩) hD
  rw [taylorWithinEval_compactifiedSlowSolution n q m x hqval hx hx0] at ht
  simp only [compactifiedSlowSolution, ite_eq_right one_ne_zero, Complex.ofReal_one,
    div_one, sub_zero, one_pow, mul_one] at ht
  apply ht.trans
  apply div_le_self (div_nonneg hC (by positivity))
  have hnfac : (1 : ℕ) ≤ n.factorial := Nat.factorial_pos n
  exact_mod_cast hnfac

end DefocusingNLS

end OAI

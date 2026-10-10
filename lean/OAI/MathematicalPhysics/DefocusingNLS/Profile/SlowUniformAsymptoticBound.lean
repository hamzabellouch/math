import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowUniformGrowth
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowAllOrdersAsymptotic

namespace OAI

/-! # Uniform leading asymptotic on compact parameter sets -/

open MeasureTheory Set

namespace DefocusingNLS

theorem exists_normalizedSlowSolution_uniform_remainder (m : ℕ) (a b M G : ℝ)
    (ha : -1 < a) (hab : a ≤ b) (hM : 0 ≤ M) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q x : ℂ,
      a ≤ q.re → q.re ≤ b → ‖(m : ℂ) - 1 - q‖ ≤ M →
      ‖(Complex.Gamma q)⁻¹‖ ≤ G → 0 ≤ x.re → 1 ≤ ‖x‖ →
        ‖normalizedSlowSolution q m x - 1‖ ≤ C / ‖x‖ := by
  let K := M * Real.exp (Real.pi * M) * (2 : ℝ) ^ (M + 1)
  let I := ‖∫ u : ℝ in Ioi 0, slowParameterMajorant a b M u‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hI : 0 ≤ I := norm_nonneg _
  refine ⟨G * K * I, mul_nonneg (mul_nonneg hG hK) hI, ?_⟩
  intro q x hqa hqb hqm hγ hx hn
  have hxpos : 0 < ‖x‖ := zero_lt_one.trans_le hn
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp hxpos.ne'
  have hi : ‖∫ u : ℝ in Ioi 0, regularizedSlowKernel q m x u‖ ≤ (K / ‖x‖) * I := by
    calc
      _ ≤ ∫ u : ℝ in Ioi 0, (K / ‖x‖) * slowParameterMajorant a b M u := by
        apply norm_integral_le_of_norm_le
          ((integrable_slowParameterMajorant a b M ha hab hM).const_mul (K / ‖x‖))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        apply (regularizedSlowKernel_bounded_parameters q m x a b M hM hqa hqb hqm hx hx0 hu).trans
        change _ ≤ (K / ‖x‖) * (Real.exp (-u) * u ^ a + Real.exp (-u) * u ^ b +
          Real.exp (-u) * u ^ (a + (M + 1)) + Real.exp (-u) * u ^ (b + (M + 1)))
        have hbase : 1 + ‖x‖⁻¹ ≤ (2 : ℝ) := by
          have hh := (inv_le_one₀ hxpos).mpr hn
          linarith
        have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 + ‖x‖⁻¹)
          hbase (by linarith : 0 ≤ M + 1)
        have hu0 : 0 ≤ u := le_of_lt hu
        dsimp [K]
        calc
          _ ≤ (M * Real.exp (Real.pi * M) / ‖x‖ * 2 ^ (M + 1)) *
              (Real.exp (-u) * u ^ a + Real.exp (-u) * u ^ b +
                Real.exp (-u) * u ^ (a + (M + 1)) + Real.exp (-u) * u ^ (b + (M + 1))) := by
            gcongr
          _ = _ := by ring
      _ = (K / ‖x‖) * ∫ u : ℝ in Ioi 0, slowParameterMajorant a b M u := integral_const_mul _ _
      _ ≤ (K / ‖x‖) * I := mul_le_mul_of_nonneg_left
        (by dsimp only [I]; exact le_abs_self _) (div_nonneg hK hxpos.le)
  have hp : x ^ q * x ^ (-q) = 1 := by
    rw [← Complex.cpow_add _ _ hx0, add_neg_cancel, Complex.cpow_zero]
  unfold normalizedSlowSolution regularizedSlowSolution
  rw [← mul_assoc, hp, one_mul, add_sub_cancel_left, norm_mul]
  calc
    _ ≤ G * ((K / ‖x‖) * I) := mul_le_mul hγ hi (norm_nonneg _) hG
    _ = _ := by ring

/-- Compactness supplies all parameter bounds, including the inverse gamma
factor at zero. No exclusion of q=0 is needed. -/
theorem exists_normalizedSlowSolution_compact_remainder (m : ℕ) (Q : Set ℂ)
    (hQ : IsCompact Q) (hq : ∀ q ∈ Q, -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Q, ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖normalizedSlowSolution q m x - 1‖ ≤ C / ‖x‖ := by
  rcases Q.eq_empty_or_nonempty with he | hne
  · subst Q
    exact ⟨0, le_rfl, by simp⟩
  obtain ⟨q₀, hq₀, hmin⟩ := hQ.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn continuous_id.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg q₀).trans (hB q₀ hq₀)
  have hγcont : Continuous (fun q : ℂ => (Complex.Gamma q)⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous
  obtain ⟨G, hG⟩ := hQ.exists_bound_of_continuousOn hγcont.continuousOn
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG q₀ hq₀)
  let M := ‖(m : ℂ) - 1‖ + B
  obtain ⟨C, hC, hb⟩ := exists_normalizedSlowSolution_uniform_remainder m q₀.re B M G
    (hq q₀ hq₀) ((Complex.re_le_norm q₀).trans (hB q₀ hq₀))
    (by dsimp [M]; positivity) hG0
  refine ⟨C, hC, ?_⟩
  intro q hqmem x hx hn
  apply hb q x (hmin hqmem) ((Complex.re_le_norm q).trans (hB q hqmem)) _ (hG q hqmem) hx hn
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (show ‖q‖ ≤ B from hB q hqmem))

theorem exists_compactifiedSlowSolution_compact_bound (m : ℕ) (Q : Set ℂ)
    (hQ : IsCompact Q) (hq : ∀ q ∈ Q, -1 < q.re) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ q ∈ Q, ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖compactifiedSlowSolution q m x t‖ ≤ A := by
  obtain ⟨C, hC, hb⟩ := exists_normalizedSlowSolution_compact_remainder m Q hQ hq
  refine ⟨C + 1, by linarith, ?_⟩
  intro q hqmem x hx hn t ht
  by_cases ht0 : t = 0
  · simp only [ht0, compactifiedSlowSolution_zero, norm_one]
    linarith
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [compactifiedSlowSolution_pos q m x htp]
    have hn' : 1 ≤ ‖x / (t : ℂ)‖ := by
      rw [norm_div, Complex.norm_of_nonneg ht.1]
      exact (le_div_iff₀ htp).mpr (by linarith [ht.2])
    calc
      _ ≤ ‖normalizedSlowSolution q m (x / (t : ℂ)) - 1‖ + 1 := by
        simpa only [norm_one] using norm_le_norm_sub_add (normalizedSlowSolution q m (x / (t : ℂ))) 1
      _ ≤ C / ‖x / (t : ℂ)‖ + 1 := add_le_add (hb q hqmem _ (slow_div_real_re_nonneg hx htp) hn') le_rfl
      _ ≤ C + 1 := add_le_add (div_le_self hC hn') le_rfl

end DefocusingNLS

end OAI

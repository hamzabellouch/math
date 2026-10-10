import OAI.NumberTheory.TwoPoint.Bounds.SmoothWindowSum

namespace OAI

/-! Summing the shorter-window estimates costs a reciprocal smooth sum,
not the number of smooth divisors. The elementary endpoint error is explicit. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma smooth_harmonic_sum_le (q K : ℕ) :
    (∑ a ∈ (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors),
      1 / (a : ℝ)) ≤ smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  let A := (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors)
  have hA (a : ℕ) (ha : a ∈ A) : 0 < a := (mem_Icc.mp (mem_filter.mp ha).1).1
  calc
    _ ≤ ∑ a ∈ A, (a : ℝ) ^ (-(1 / 2) : ℝ) := by
      apply sum_le_sum
      intro a ha
      rw [one_div, ← Real.rpow_neg_one]
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hA a ha
      · norm_num
    _ ≤ _ := smooth_reciprocal_sum_le q.primeFactors A
      (fun p hp => Nat.prime_of_mem_primeFactors hp) (1 / 2) (by norm_num)
      (fun a ha => Nat.mem_factoredNumbers_of_primeFactors_subset (hA a ha).ne'
        (mem_filter.mp ha).2)

lemma dilation_window_count_bound (a D Y : ℕ)
    (ha : 0 < a) (haD : a ≤ D) (haY : a ≤ Y) :
    (a : ℝ) * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) ≤
      4 * (D : ℝ) * Y / a := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hd : (1 : ℝ) ≤ (D : ℝ) / a := (le_div_iff₀ hap).mpr (by simpa only [one_mul] using (show (a : ℝ) ≤ D by exact_mod_cast haD))
  have hy : (1 : ℝ) ≤ (Y : ℝ) / a := (le_div_iff₀ hap).mpr (by simpa only [one_mul] using (show (a : ℝ) ≤ Y by exact_mod_cast haY))
  have hD : ((D / a + 1 : ℕ) : ℝ) ≤ 2 * (D : ℝ) / a := by
    have hh : ((D / a : ℕ) : ℝ) ≤ (D : ℝ) / a := Nat.cast_div_le
    push_cast
    calc
      (D / a : ℕ) + (1 : ℝ) ≤ (D : ℝ) / a + 1 := add_le_add hh le_rfl
      _ ≤ 2 * ((D : ℝ) / a) := by linarith only [hd]
      _ = _ := by ring
  have hY : ((Y / a + 1 : ℕ) : ℝ) ≤ 2 * (Y : ℝ) / a := by
    have hh : ((Y / a : ℕ) : ℝ) ≤ (Y : ℝ) / a := Nat.cast_div_le
    push_cast
    calc
      (Y / a : ℕ) + (1 : ℝ) ≤ (Y : ℝ) / a + 1 := add_le_add hh le_rfl
      _ ≤ 2 * ((Y : ℝ) / a) := by linarith only [hy]
      _ = _ := by ring
  calc
    _ ≤ (a : ℝ) * (2 * D / a) * (2 * Y / a) := by gcongr
    _ = _ := by field_simp; ring

/-- The finite analytic assembly used for a dilated nonpretentious factor.
`hbase` is subsequently supplied by the published MRT theorem, uniformly in
the original function's finite-prime changes. -/
theorem smooth_dilation_window_bound {f : ℕ → ℂ}
    (hf : Multiplicative f) (hfb : OneBounded f)
    (q K D Y : ℕ) (hq : 0 < q) (hK : 0 < K)
    (hKD : K ≤ D) (hDY : D ≤ Y) (C E : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hbase : ∀ a ∈ Icc 1 K, ∀ β : ℝ,
      (∑ m ∈ range (Y / a + 1),
        ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) β m‖) ≤
        C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) * E)
    (α : ℝ) :
    (∑ v ∈ range Y, ‖shortWindowSum (fun n => f (q * n)) D α v‖) ≤
      4 * C * D * Y * E * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) +
        (K : ℝ) * Y + 2 * D * Y * (K : ℝ) ^ (-(1 / 2) : ℝ) *
          smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  let A := (Icc 1 K).filter (fun a => a.primeFactors ⊆ q.primeFactors)
  have hcoeff : 0 ≤ 4 * C * D * Y * E := by positivity
  have hs : (∑ a ∈ A, ((a : ℝ) * (∑ m ∈ range (Y / a + 1),
      ‖shortWindowSum (coprimeRestriction q f) (D / a + 1) (a * α) m‖) + Y)) ≤
      4 * C * D * Y * E * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) +
        (K : ℝ) * Y := by
    calc
      _ ≤ ∑ a ∈ A, (4 * C * D * Y * E * (1 / (a : ℝ)) + Y) := by
        apply sum_le_sum
        intro a ha
        have haI := (mem_filter.mp ha).1
        have hap : 0 < a := (mem_Icc.mp haI).1
        have haD := (mem_Icc.mp haI).2.trans hKD
        have haY := haD.trans hDY
        apply add_le_add ?_ le_rfl
        calc
          _ ≤ (a : ℝ) * (C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) * E) :=
            mul_le_mul_of_nonneg_left (hbase a haI _) (Nat.cast_nonneg a)
          _ = (C * E) * ((a : ℝ) * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ)) := by ring
          _ ≤ (C * E) * (4 * (D : ℝ) * Y / a) :=
            mul_le_mul_of_nonneg_left (dilation_window_count_bound a D Y hap haD haY)
              (mul_nonneg hC hE)
          _ = _ := by ring
      _ = 4 * C * D * Y * E * (∑ a ∈ A, 1 / (a : ℝ)) + (A.card : ℝ) * Y := by
        rw [sum_add_distrib, ← mul_sum]
        simp only [sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (smooth_harmonic_sum_le q K) hcoeff
        · apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg Y)
          have hsub : A ⊆ Icc 1 K := filter_subset _ _
          have hcard : A.card ≤ K := by simpa using card_le_card hsub
          exact_mod_cast hcard
  have htail : (D : ℝ) * (Y + D) * (K : ℝ) ^ (-(1 / 2) : ℝ) *
      smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) ≤
      2 * D * Y * (K : ℝ) ^ (-(1 / 2) : ℝ) *
        smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
    have hDYr : (D : ℝ) ≤ Y := by exact_mod_cast hDY
    have hM := smoothReciprocalProduct_nonneg q.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp) (1 / 2) (by norm_num)
    have hh : (D : ℝ) * (Y + D) ≤ 2 * D * Y := by nlinarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (Nat.cast_nonneg K) _)) hM
  exact (smooth_dilation_window_sum hf hfb q K D Y hq hK α).trans
    ((add_le_add hs htail).trans_eq (by ring))

end TwoPointCorrelations

end OAI

import OAI.NumberTheory.Ostmann.ZeroDensity.DensityHybridIntegral

namespace OAI

/-! # A hybrid large sieve with an absolute constant

The character and height variables are averaged simultaneously. The proof uses
short logarithmic windows and the already proved finite additive large sieve.
-/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators SchwartzMap FourierTransform Classical

 theorem hybrid_multiplicative_large_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
          a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t))‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨c, W, hc, hW, _, hWlower⟩ := exists_density_localizer
  let K : ℝ := ∫ x : ℝ, ‖W x‖ ^ 2
  have hK : 0 ≤ K := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨3 * (K + 1) / c ^ 2, by positivity, ?_⟩
  intro N Q hQ T hT a F hF
  have hTpos : 0 < T := by linarith
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hh : 0 < T⁻¹ := inv_pos.mpr hTpos
  have hb := density_hybrid_window N Q hQ W c T⁻¹ T hc hh
    (by rw [inv_mul_cancel₀ hTpos.ne']) hW hWlower a F hF
  let E : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd : 0 < T⁻¹ ^ 2 * c ^ 2 := mul_pos (pow_pos hh 2) hc2
  have hb' := (le_div_iff₀' hd).mpr hb
  have hid : ((2 * (N : ℝ) * T⁻¹ + (Q : ℝ) ^ 2 + 2) * T⁻¹ * K * E) /
      (T⁻¹ ^ 2 * c ^ 2) =
        (K / c ^ 2) * (2 * N + ((Q : ℝ) ^ 2 + 2) * T) * E := by
    field_simp
    ring
  change _ ≤ ((2 * (N : ℝ) * T⁻¹ + (Q : ℝ) ^ 2 + 2) * T⁻¹ * K * E) /
    (T⁻¹ ^ 2 * c ^ 2) at hb'
  rw [hid] at hb'
  apply hb'.trans
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq2 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
  have hsize : 2 * (N : ℝ) + ((Q : ℝ) ^ 2 + 2) * T ≤
      3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N, mul_nonneg (by linarith : 0 ≤ (Q : ℝ) ^ 2 - 1) hTpos.le]
  have hbase : 0 ≤ (N : ℝ) + (Q : ℝ) ^ 2 * T := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hsize (div_nonneg hK hc2.le)
  have hsecond := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (by linarith : K ≤ K + 1) hc2.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hbase)
  have hbound : (K / c ^ 2) * (2 * (N : ℝ) + ((Q : ℝ) ^ 2 + 2) * T) ≤
      (3 * (K + 1) / c ^ 2) * ((N : ℝ) + (Q : ℝ) ^ 2 * T) := by
    calc
      _ ≤ (K / c ^ 2) * (3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T)) := hfirst
      _ ≤ ((K + 1) / c ^ 2) * (3 * ((N : ℝ) + (Q : ℝ) ^ 2 * T)) := hsecond
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right hbound hE

end Ostmann

end OAI
